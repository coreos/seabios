//  Implementation of the TCG BIOS extension according to the specification
//  described in specs found at
//  http://www.trustedcomputinggroup.org/resources/pc_client_work_group_specific_implementation_specification_for_conventional_bios
//
//  Copyright (C) 2006-2011, 2014, 2015 IBM Corporation
//
//  Authors:
//      Stefan Berger <stefanb@linux.vnet.ibm.com>
//
// This file may be distributed under the terms of the GNU LGPLv3 license.

#include "bregs.h" // struct bregs
#include "byteorder.h" // cpu_to_*
#include "config.h" // CONFIG_TCGBIOS
#include "farptr.h" // MAKE_FLATPTR
#include "fw/paravirt.h" // runningOnXen
#include "hw/tpm_drivers.h" // tpm_drivers[]
#include "output.h" // dprintf
#include "sha1.h" // sha1
#include "std/acpi.h"  // RSDP_SIGNATURE, rsdt_descriptor
#include "std/smbios.h" // struct smbios_entry_point
#include "std/tcg.h" // TCG_PC_LOGOVERFLOW
#include "string.h" // checksum
#include "tcgbios.h"// tpm_*, prototypes
#include "util.h" // printf, get_keystroke
#include "stacks.h" // wait_threads, reset

#if CONFIG_TCGBIOS_QEMU

/****************************************************************
 * ACPI TCPA table interface
 ****************************************************************/

struct {
    /* length of the TCPA log buffer */
    u32           log_area_minimum_length;

    /* start address of TCPA log buffer */
    u8 *          log_area_start_address;

    /* number of log entries written */
    u32           entry_count;

    /* address to write next log entry to */
    u8 *          log_area_next_entry;

    /* address of last entry written (need for TCG_StatusCheck) */
    u8 *          log_area_last_entry;
} tpm_state VARLOW;

static struct tcpa_descriptor_rev2 *
find_tcpa_by_rsdp(struct rsdp_descriptor *rsdp)
{
    if (!rsdp) {
        dprintf(DEBUG_tcg,
                "TCGBIOS: RSDP was NOT found! -- Disabling interface.\n");
        return NULL;
    }
    struct rsdt_descriptor *rsdt = (void*)rsdp->rsdt_physical_address;
    if (!rsdt)
        return NULL;

    u32 length = rsdt->length;
    u16 off = offsetof(struct rsdt_descriptor, entry);
    u32 ctr = 0;
    while ((off + sizeof(rsdt->entry[0])) <= length) {
        /* try all pointers to structures */
        struct tcpa_descriptor_rev2 *tcpa = (void*)rsdt->entry[ctr];

        /* valid TCPA ACPI table ? */
        if (tcpa->signature == TCPA_SIGNATURE
            && checksum(tcpa, tcpa->length) == 0)
            return tcpa;

        off += sizeof(rsdt->entry[0]);
        ctr++;
    }

    dprintf(DEBUG_tcg, "TCGBIOS: TCPA ACPI was NOT found!\n");
    return NULL;
}

static int
tpm_tcpa_probe(void)
{
    int i;
    struct tcpa_descriptor_rev2 *tcpa = find_tcpa_by_rsdp(RsdpAddr);
    if (!tcpa)
        return -1;

    u8 *log_area_start_address = (u8*)(long)tcpa->log_area_start_address;
    u32 log_area_minimum_length = tcpa->log_area_minimum_length;
    if (!log_area_start_address || !log_area_minimum_length)
        return -1;

    tpm_state.log_area_start_address = log_area_start_address;
    tpm_state.log_area_next_entry = log_area_start_address;
    tpm_state.log_area_minimum_length = log_area_minimum_length;
    tpm_state.log_area_last_entry = NULL;
    tpm_state.entry_count = 0;
    struct pcpes *pcpes = (void*)tpm_state.log_area_next_entry;
    while (pcpes->eventdatasize) {
	    tpm_state.log_area_last_entry = tpm_state.log_area_next_entry;
	    tpm_state.log_area_next_entry += pcpes->eventdatasize +
		    sizeof(struct pcpes);
	    tpm_state.entry_count++;
	    pcpes = (void *)tpm_state.log_area_next_entry;
    }
    return 0;
}

static int
tpm_log_event(struct tcg_pcr_event2_sha1 *entry, const void *event)
{
    dprintf(DEBUG_tcg, "TCGBIOS: LASA = %p, next entry = %p\n",
            tpm_state.log_area_start_address, tpm_state.log_area_next_entry);

    if (tpm_state.log_area_next_entry == NULL)
        return -1;

    u32 size = sizeof(*entry) + entry->eventdatasize;
    u32 logsize = (tpm_state.log_area_next_entry + size
                   - tpm_state.log_area_start_address);
    if (logsize > tpm_state.log_area_minimum_length) {
        dprintf(DEBUG_tcg, "TCGBIOS: LOG OVERFLOW: size = %d\n", size);
        return -1;
    }

    struct pcpes *pcpes = (void*)tpm_state.log_area_next_entry;
    pcpes->pcrindex = entry->pcrindex;
    pcpes->eventtype = entry->eventtype;
    memcpy(pcpes->digest, entry->digests[0].sha1, sizeof(pcpes->digest));
    pcpes->eventdatasize = entry->eventdatasize;
    memcpy(pcpes->event, event, entry->eventdatasize);
    size = sizeof(*pcpes) + entry->eventdatasize;

    tpm_state.log_area_last_entry = tpm_state.log_area_next_entry;
    tpm_state.log_area_next_entry += size;
    tpm_state.entry_count++;

    return 0;
 }


/****************************************************************
 * Helper functions
 ****************************************************************/

static int
tpm_extend(u32 pcrindex, const u8 *digest)
{
    int i;
    outb(pcrindex, 0x620);
    for (i=0; i<20; i++) {
        outb(digest[i], 0x621);
    }
    return 0;
}

/*
 * Add a measurement to the log; the data at data_seg:data/length are
 * appended to the TCG_PCClientPCREventStruct
 *
 * Input parameters:
 *  pcrindex   : which PCR to extend
 *  event_type : type of event; specs section on 'Event Types'
 *  event       : pointer to info (e.g., string) to be added to log as-is
 *  event_length: length of the event
 *  hashdata    : pointer to the data to be hashed
 *  hashdata_length: length of the data to be hashed
 */
static void
tpm_add_measurement_to_log(u32 pcrindex, u32 event_type,
                           const char *event, u32 event_length,
                           const u8 *hashdata, u32 hashdata_length)
{
    struct tcg_pcr_event2_sha1 entry = {
        .pcrindex = pcrindex,
        .eventtype = event_type,
        .eventdatasize = event_length,
        .count = 1,
        .digests[0].hashtype  = TPM2_ALG_SHA1,
    };
    sha1(hashdata, hashdata_length, entry.digests[0].sha1);
    int ret = tpm_extend(entry.pcrindex, entry.digests[0].sha1);
    if (ret) {
        return;
    }
    tpm_log_event(&entry, event);
}

/****************************************************************
 * Setup and Measurements
 ****************************************************************/

// Add an EV_ACTION measurement to the list of measurements
static void
tpm_add_action(u32 pcrIndex, const char *string)
{
    u32 len = strlen(string);
    tpm_add_measurement_to_log(pcrIndex, EV_ACTION,
                               string, len, (u8 *)string, len);
}

/*
 * Add event separators for PCRs 0 to 7; specs on 'Measuring Boot Events'
 */
static void
tpm_add_event_separators(void)
{
    static const u8 evt_separator[] = {0xff,0xff,0xff,0xff};
    u32 pcrIndex;
    for (pcrIndex = 0; pcrIndex <= 7; pcrIndex++)
        tpm_add_measurement_to_log(pcrIndex, EV_SEPARATOR,
                                   NULL, 0,
                                   evt_separator,
                                   sizeof(evt_separator));
}

static void
tpm_smbios_measure(void)
{
    struct pcctes pcctes = {
        .eventid = 1,
        .eventdatasize = SHA1_BUFSIZE,
    };
    struct smbios_entry_point *sep = SMBiosAddr;

    dprintf(DEBUG_tcg, "TCGBIOS: SMBIOS at %p\n", sep);

    if (!sep)
        return;

    sha1((const u8 *)sep->structure_table_address,
         sep->structure_table_length, pcctes.digest);
    tpm_add_measurement_to_log(1,
                               EV_EVENT_TAG,
                               (const char *)&pcctes, sizeof(pcctes),
                               (u8 *)&pcctes, sizeof(pcctes));
}

void
tpm_setup(void)
{
    dprintf(1, "********** TPM SETUP\n");
    tpm_tcpa_probe();
    tpm_smbios_measure();
    tpm_add_action(2, "Start Option ROM Scan");
}

/*
 * Add measurement to the log about an option rom
 */
void
tpm_option_rom(const void *addr, u32 len)
{
    struct pcctes_romex pcctes = {
        .eventid = 7,
        .eventdatasize = sizeof(u16) + sizeof(u16) + SHA1_BUFSIZE,
    };
    sha1((const u8 *)addr, len, pcctes.digest);
    tpm_add_measurement_to_log(2,
                               EV_EVENT_TAG,
                               (const char *)&pcctes, sizeof(pcctes),
                               (u8 *)&pcctes, sizeof(pcctes));
}

void
tpm_add_bcv(u32 bootdrv, const u8 *addr, u32 length)
{
    if (length < 0x200)
        return;

    const char *string = "Booting BCV device 00h (Floppy)";
    if (bootdrv == 0x80)
        string = "Booting BCV device 80h (HDD)";
    tpm_add_action(4, string);

    /* specs: see section 'Hard Disk Device or Hard Disk-Like Devices' */
    /* equivalent to: dd if=/dev/hda ibs=1 count=440 | sha1sum */
    string = "MBR";
    tpm_add_measurement_to_log(4, EV_IPL,
                               string, strlen(string),
                               addr, 0x1b8);

    /* equivalent to: dd if=/dev/hda ibs=1 count=72 skip=440 | sha1sum */
    string = "MBR PARTITION_TABLE";
    tpm_add_measurement_to_log(5, EV_IPL_PARTITION_DATA,
                               string, strlen(string),
                               addr + 0x1b8, 0x48);
}

void
tpm_add_cdrom(u32 bootdrv, const u8 *addr, u32 length)
{
    tpm_add_action(4, "Booting from CD ROM device");

    /* specs: see section 'El Torito' */
    const char *string = "EL TORITO IPL";
    tpm_add_measurement_to_log(4, EV_IPL,
                               string, strlen(string),
                               addr, length);
}

void
tpm_add_cdrom_catalog(const u8 *addr, u32 length)
{
    tpm_add_action(4, "Booting from CD ROM device");

    /* specs: see section 'El Torito' */
    const char *string = "BOOT CATALOG";
    tpm_add_measurement_to_log(5, EV_IPL_PARTITION_DATA,
                               string, strlen(string),
                               addr, length);
}

/****************************************************************
 * BIOS interface
 ****************************************************************/

u8 TPM_interface_shutdown VARLOW;

static inline void *input_buf32(struct bregs *regs)
{
    return MAKE_FLATPTR(regs->es, regs->di);
}

static inline void *output_buf32(struct bregs *regs)
{
    return MAKE_FLATPTR(regs->ds, regs->si);
}

static u32
hash_log_extend(struct pcpes *pcpes, const void *hashdata, u32 hashdata_length
                , void *event, int extend)
{
    if (pcpes->pcrindex >= 24)
        return TCG_INVALID_INPUT_PARA;
    if (hashdata)
        sha1(hashdata, hashdata_length, pcpes->digest);
    if (extend) {
        int ret = tpm_extend(pcpes->pcrindex, pcpes->digest);
        if (ret)
            return TCG_TCG_COMMAND_ERROR;
    }
    struct tcg_pcr_event2_sha1 entry = {
        .pcrindex = pcpes->pcrindex,
        .eventtype = pcpes->eventtype,
        .eventdatasize = pcpes->eventdatasize,
        .count = 1,
        .digests[0].hashtype = TPM2_ALG_SHA1,
    };
    memcpy(entry.digests[0].sha1, pcpes->digest, sizeof(entry.digests[0].sha1));
    int ret = tpm_log_event(&entry, pcpes->event);
    if (ret)
        return TCG_PC_LOGOVERFLOW;
    return 0;
}

static u32
hash_log_extend_event_int(const struct hleei_short *hleei_s,
                          struct hleeo *hleeo)
{
    u32 rc = 0;
    struct hleo hleo;
    struct hleei_long *hleei_l = (struct hleei_long *)hleei_s;
    const void *logdataptr;
    u32 logdatalen;
    struct pcpes *pcpes;
    u32 pcrindex;

    /* short or long version? */
    switch (hleei_s->ipblength) {
    case sizeof(struct hleei_short):
        /* short */
        logdataptr = hleei_s->logdataptr;
        logdatalen = hleei_s->logdatalen;
        pcrindex = hleei_s->pcrindex;
    break;

    case sizeof(struct hleei_long):
        /* long */
        logdataptr = hleei_l->logdataptr;
        logdatalen = hleei_l->logdatalen;
        pcrindex = hleei_l->pcrindex;
    break;

    default:
        /* bad input block */
        rc = TCG_INVALID_INPUT_PARA;
        goto err_exit;
    }

    pcpes = (struct pcpes *)logdataptr;

    if (pcpes->pcrindex != pcrindex
        || logdatalen != sizeof(*pcpes) + pcpes->eventdatasize) {
        rc = TCG_INVALID_INPUT_PARA;
        goto err_exit;
    }
    rc = hash_log_extend(pcpes, hleei_s->hashdataptr, hleei_s->hashdatalen
                         , pcpes->event, 1);
    if (rc)
        goto err_exit;

    hleeo->opblength = sizeof(struct hleeo);
    hleeo->reserved  = 0;
    hleeo->eventnumber = hleo.eventnumber;
    memcpy(hleeo->digest, pcpes->digest, sizeof(hleeo->digest));

err_exit:
    if (rc != 0) {
        hleeo->opblength = 4;
        hleeo->reserved  = 0;
    }

    return rc;
}

static u32
hash_log_event_int(const struct hlei *hlei, struct hleo *hleo)
{
    u32 rc = 0;
    u16 size;
    struct pcpes *pcpes;

    size = hlei->ipblength;
    if (size != sizeof(*hlei)) {
        rc = TCG_INVALID_INPUT_PARA;
        goto err_exit;
    }

    pcpes = (struct pcpes *)hlei->logdataptr;

    if (pcpes->pcrindex != hlei->pcrindex
        || pcpes->eventtype != hlei->logeventtype
        || hlei->logdatalen != sizeof(*pcpes) + pcpes->eventdatasize) {
        rc = TCG_INVALID_INPUT_PARA;
        goto err_exit;
    }
    rc = hash_log_extend(pcpes, hlei->hashdataptr, hlei->hashdatalen
                         , pcpes->event, 0);
    if (rc)
        goto err_exit;

    /* updating the log was fine */
    hleo->opblength = sizeof(struct hleo);
    hleo->reserved  = 0;
    hleo->eventnumber = tpm_state.entry_count;

err_exit:
    if (rc != 0) {
        hleo->opblength = 2;
        hleo->reserved = 0;
    }

    return rc;
}

static u32
hash_all_int(const struct hai *hai, u8 *hash)
{
    if (hai->ipblength != sizeof(struct hai) ||
        hai->hashdataptr == 0 ||
        hai->hashdatalen == 0 ||
        hai->algorithmid != TPM_ALG_SHA)
        return TCG_INVALID_INPUT_PARA;

    sha1((const u8 *)hai->hashdataptr, hai->hashdatalen, hash);
    return 0;
}

static u32
compact_hash_log_extend_event_int(u8 *buffer,
                                  u32 info,
                                  u32 length,
                                  u32 pcrindex,
                                  u32 *edx_ptr)
{
    struct pcpes pcpes = {
        .pcrindex      = pcrindex,
        .eventtype     = EV_COMPACT_HASH,
        .eventdatasize = sizeof(info),
    };
    u32 rc = hash_log_extend(&pcpes, buffer, length, &info, 1);
    if (rc)
        return rc;

    *edx_ptr = tpm_state.entry_count;
    return 0;
}

void VISIBLE32FLAT
tpm_interrupt_handler32(struct bregs *regs)
{
    if (!CONFIG_TCGBIOS_QEMU)
        return;

    set_cf(regs, 0);

    if (TPM_interface_shutdown && regs->al) {
        regs->eax = TCG_INTERFACE_SHUTDOWN;
        return;
    }

    switch ((enum irq_ids)regs->al) {
    case TCG_StatusCheck:
        regs->eax = 0;
	regs->ebx = TCG_MAGIC;
	regs->ch = TCG_VERSION_MAJOR;
	regs->cl = TCG_VERSION_MINOR;
	regs->edx = 0x0;
	regs->esi = (u32)tpm_state.log_area_start_address;
	regs->edi = (u32)tpm_state.log_area_last_entry;
        break;

    case TCG_HashLogExtendEvent:
        regs->eax =
            hash_log_extend_event_int(
                  (struct hleei_short *)input_buf32(regs),
                  (struct hleeo *)output_buf32(regs));
        break;

    case TCG_HashLogEvent:
        regs->eax = hash_log_event_int((struct hlei*)input_buf32(regs),
                                       (struct hleo*)output_buf32(regs));
        break;

    case TCG_HashAll:
        regs->eax =
            hash_all_int((struct hai*)input_buf32(regs),
                          (u8 *)output_buf32(regs));
        break;

    case TCG_CompactHashLogExtendEvent:
        regs->eax =
          compact_hash_log_extend_event_int((u8 *)input_buf32(regs),
                                            regs->esi,
                                            regs->ecx,
                                            regs->edx,
                                            &regs->edx);
        break;

    default:
        set_cf(regs, 1);
    }

    return;
}

int
tpm_can_show_menu(void)
{
    return 0;
}

void
tpm_prepboot(void)
{
    tpm_add_event_separators();
    return;
}

void
tpm_s3_resume(void)
{
    return;
}
#endif //CONFIG_TCGBIOS_QEMU
