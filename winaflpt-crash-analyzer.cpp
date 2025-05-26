/*
   WinAFL-PT Crash Analyzer & Trace Slicer
   ------------------------------------------------

   Created by Gyumin Baek <guminb@ajou.ac.kr> (2025)

   Copyright 2025 Gyumin Baek. All Rights Reserved.

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

*/


#define  _CRT_SECURE_NO_WARNINGS

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <stdint.h>
#include <dbgeng.h>
#include <direct.h>

#include "windows.h"
#include "debug.h"
#include "types.h"

#include "psapi.h"
#include "dbghelp.h"

extern "C" {
    #include "intel-pt.h"
    #include "libipt.h"
    #include "pt_cpu.h"
    #include "pt_cpuid.h"
    #include "pt_block_decoder.h"
    #include "pt_insn_decoder.h"
}

#define MAX_FRAMES 64
#define MAX_FILES 5000
#define TRACE_BUFFER_SIZE_DEFAULT (128*1024) //should be a power of 2

#define debug_suffix "_debug.txt"
#define ptlog_suffix "_ptlog.pt"
#define procdump_suffix "_process.dmp"

#define RELEASE(x) if(x){ x->Release(); x = NULL; }

typedef enum {
    MODE_32 = 0,
    MODE_64 = 1
} mode_bit_t;

typedef struct{
    char call_site[MAX_PATH];
    uint64_t address;
}callstack_frame;

typedef struct _crash_info_t{
    char crash_input_filename[MAX_PATH];
    char crash_debug_filename[MAX_PATH];
    char crash_procdump_filename[MAX_PATH];
    char crash_ptlog_filename[MAX_PATH];
    int frame_count;
    DWORD ret_exception_code;
    DWORD crash_thread_id;
    mode_bit_t mode;
    bool unique;
    callstack_frame frames[MAX_FRAMES];
}crash_info_t;

typedef struct {
    char **files;
    int count;
} file_list;

typedef struct _module_info_t {
    char module_name[MAX_PATH];
    int isid;
    void *base;
    size_t size;
    struct _module_info_t *next;
} module_info_t;

static struct pt_image_section_cache *section_cache = NULL;
static struct pt_image *image = NULL;
static module_info_t *all_modules = NULL;
static unsigned char *trace_buffer;
static size_t trace_size;
const char *out_dir = NULL;

IDebugClient   *g_DebugClient  = NULL;
IDebugControl  *g_DebugControl = NULL;
IDebugSymbols  *g_DebugSymbols = NULL;
IDebugDataSpaces *g_DebugDataSpaces = NULL;

unsigned char psb[16] = {
    0x02, 0x82, 0x02, 0x82, 0x02, 0x82, 0x02, 0x82,
    0x02, 0x82, 0x02, 0x82, 0x02, 0x82, 0x02, 0x82
};

char coverage_module[MAX_PATH] = {0};

file_list *slice_list = NULL;
extern "C" int deduplicate_root_cause_seeds(const char **sliceFiles, int sliceCount, int *uniqueIndices);
extern "C" void analyze_trace_file(const char* trace_path, const char* coverage_module, const char* output_filepath, bool is64bit);

HRESULT InitializeDbgEng(void){
    HRESULT hr = DebugCreate(__uuidof(IDebugClient), (void**)&g_DebugClient);
    if (FAILED(hr)) {
    FATAL("DebugCreate failed: 0x%08x\n", hr);
    }

    hr = g_DebugClient->QueryInterface(__uuidof(IDebugControl), (void**)&g_DebugControl);
    if (FAILED(hr)) {
    FATAL("QueryInterface(IDebugControl) failed: 0x%08x\n", hr);
    }

    hr = g_DebugClient->QueryInterface(__uuidof(IDebugSymbols), (void**)&g_DebugSymbols);
    if (FAILED(hr)) {
    FATAL("QueryInterface(IDebugSymbols) failed: 0x%08x\n", hr);
    }
    hr = g_DebugClient->QueryInterface(__uuidof(IDebugDataSpaces), (void**)&g_DebugDataSpaces);
    if (FAILED(hr)) {
    FATAL("QueryInterface(IDebugDataSpaces) failed: 0x%08x\n", hr);
    }
    return S_OK;
}
 
 
HRESULT OpenDumpFileAndWait(const char *dumpFile){

    HRESULT hr = g_DebugClient->OpenDumpFile(dumpFile);
    if (FAILED(hr)) {
        FATAL("OpenDumpFileA failed for %s: 0x%08x\n", dumpFile, hr);
    }

    hr = g_DebugControl->WaitForEvent(0, INFINITE);
    if (FAILED(hr)) {
        FATAL("WaitForEvent failed: 0x%08x\n", hr);
    }
    return S_OK;
}

void PrintSymbolAndDisassembly(ULONG64 address, FILE* output_file){
    char symbolBuffer[1024] = {0};
    ULONG64 displacement = 0;
    HRESULT hr = g_DebugSymbols->GetNameByOffset(address, symbolBuffer, sizeof(symbolBuffer), NULL, &displacement);
    if (FAILED(hr)) {
        FATAL("GetNameByOffset failed for 0x%llx: 0x%08x\n", address, hr);
    }

    char disasmBuffer[1024] = {0};
    ULONG disasmSize = 0;
    ULONG64 endOffset = 0;
    hr = g_DebugControl->Disassemble(address, 0, disasmBuffer, sizeof(disasmBuffer), &disasmSize, &endOffset);
    if (FAILED(hr)) {
        FATAL("Disassemble failed for 0x%llx: 0x%08x\n", address, hr);
    }

    if(!output_file){
        printf("%s+0x%llx:\n", symbolBuffer, displacement);
        printf("%s\n\n", disasmBuffer);
    }
    else{
        fprintf(output_file, "%s+0x%llx:\n", symbolBuffer, displacement);
        fprintf(output_file, "%s\n\n", disasmBuffer);
    }

}


void parse_options(int argc, const char *argv[]) {
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-coverage_module") == 0) {
            if (i + 1 < argc) {
                strncpy(coverage_module, argv[++i], MAX_PATH - 1);
                coverage_module[MAX_PATH - 1] = '\0';
            } else {
                FATAL("Error: -coverage_module option needs module name\n");
            }
        }
    }
}

void free_all_modules(void) {
    module_info_t *current = all_modules;
    while (current) {
        module_info_t *next = current->next;
        free(current);
        current = next;
    }
    all_modules = NULL;
}

file_list *get_file_list(const char *folder, const char *pattern) {
    WIN32_FIND_DATAA findFileData;
    HANDLE hFind = INVALID_HANDLE_VALUE;
    char searchPattern[MAX_PATH];
    file_list *list = NULL;
    
    list = (file_list *)malloc(sizeof(file_list));
    if (!list) {
        FATAL("Memory allocation failed, GLE=%x\n", GetLastError());
    }

    list->files = (char **)malloc(sizeof(char*) * MAX_FILES);
    if (!list->files) {
        free(list);
        FATAL("Memory allocation failed, GLE=%x\n", GetLastError());
    }
    list->count = 0;
    snprintf(searchPattern, MAX_PATH, "%s\\%s", folder, pattern);
    
    hFind = FindFirstFileA(searchPattern, &findFileData);
    if (hFind == INVALID_HANDLE_VALUE) {
        free(list->files);
        free(list);
        FATAL("FindFirstFile failed, GLE=%x\n", GetLastError());
    }

    do {

        if (!(findFileData.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)) {
            if (list->count < MAX_FILES) {
                list->files[list->count] = (char*)malloc(MAX_PATH);
                if (!list->files[list->count]) {
                    FATAL("Memory allocation failed, GLE=%x\n", GetLastError());
                }
                snprintf(list->files[list->count], MAX_PATH, "%s\\%s", folder, findFileData.cFileName);
                list->count++;
            } else {
                break;
            }
        }
    } while (FindNextFileA(hFind, &findFileData) != 0);
    
    FindClose(hFind);
    return list;
}

void free_file_list(file_list *list) {
    if (list) {
        for (int i = 0; i < list->count; i++) {
            free(list->files[i]);
        }
        free(list->files);
        free(list);
    }
}

void print_files(file_list *list){
    if(list){
        for(int i=0; i < list->count; i++){
            printf("%s\n", list->files[i]);
        }
    }
}

int parse_crash_debug_file(const char *filename, crash_info_t *out_crash) {
    FILE *fp = fopen(filename, "r");
    if (!fp) {
        FATAL("Error opening file: %s, GLE=%x\n", filename, GetLastError());
    }


    strncpy(out_crash->crash_debug_filename, filename, MAX_PATH - 1);
    out_crash->crash_debug_filename[MAX_PATH - 1] = '\0';

    char *pos = (char *)strstr(filename, debug_suffix);
    if (pos != NULL) {
        size_t prefix_len = pos - filename;
        if (prefix_len > MAX_PATH - 1)
            prefix_len = MAX_PATH - 1;
        strncpy(out_crash->crash_input_filename, filename, prefix_len);
        out_crash->crash_input_filename[prefix_len] = '\0';

        strncpy(out_crash->crash_ptlog_filename, filename, prefix_len);
        out_crash->crash_ptlog_filename[prefix_len] = '\0';
        
        strncpy(out_crash->crash_procdump_filename, filename, prefix_len);
        out_crash->crash_procdump_filename[prefix_len] = '\0';

        strncat(out_crash->crash_ptlog_filename, ptlog_suffix, MAX_PATH - strlen(out_crash->crash_ptlog_filename) - 1);
        strncat(out_crash->crash_procdump_filename, procdump_suffix, MAX_PATH - strlen(out_crash->crash_procdump_filename) - 1);
    }

    out_crash->frame_count = 0;
    out_crash->ret_exception_code = 0;
    out_crash->crash_thread_id = 0;
    out_crash->mode = MODE_32;
    out_crash->unique = 1;

    char line[1024];
    bool in_callstack = false;
    while (fgets(line, sizeof(line), fp)) {

        size_t len = strlen(line);
        if (len > 0 && line[len-1] == '\n'){
            line[len-1] = '\0';
        }
        
        if (strstr(line, "Exception Code:") != NULL) {
            unsigned int code;
            if (sscanf(line, "Exception Code: 0x%x", &code) == 1) {
                out_crash->ret_exception_code = code;
            }
            continue;
        }
        
        if (strstr(line, "Crash Thread ID:") != NULL) {
            DWORD tid;
            if (sscanf(line, "Crash Thread ID: 0x%x", &tid) == 1) {
                out_crash->crash_thread_id = tid;
            }
            continue;
        }

        if (strstr(line, "EIP=") != NULL) {
            out_crash->mode = MODE_32;
            continue;
        } else if (strstr(line, "RIP=") != NULL) {
            out_crash->mode = MODE_64;
            continue;
        }

        if (strstr(line, "-------------------------------------------") != NULL) {

            if (in_callstack)
                continue;
            else {
                in_callstack = true;
                continue;
            }
        }

        if (in_callstack && strncmp(line, "[#", 2) == 0) {
            if (out_crash->frame_count >= MAX_FRAMES) {

                break;
            }
            callstack_frame *frame = &out_crash->frames[out_crash->frame_count];

            if (sscanf(line, "[#]%*d %255s - 0x%llx", frame->call_site, &frame->address) == 2) {
                out_crash->frame_count++;
            }
        }
    }
    fclose(fp);
    return 0;
}

bool compare_callstacks(const crash_info_t *c1, const crash_info_t *c2) {
    if (c1->frame_count != c2->frame_count) return false;
    for (int i = 0; i < c1->frame_count; i++) {
        if (strcmp(c1->frames[i].call_site, c2->frames[i].call_site) != 0)
            return false;
        if (c1->frames[i].address != c2->frames[i].address)
            return false;
    }
    return true;
}

void remove_duplicate_crashes(crash_info_t *crashes, int count, int unique_flags[], int *unique_count) {
    for (int i = 0; i < count; i++) {
        crashes[i].unique = true;
    }
    
    for (int i = 0; i < count; i++) {
        if (!crashes[i].unique)
            continue;
        for (int j = i + 1; j < count; j++) {
            if (compare_callstacks(&crashes[i], &crashes[j])) {
                crashes[j].unique = false;
            }
        }
    }
    
    int ucount = 0;
    for (int i = 0; i < count; i++) {
        if (crashes[i].unique) {
            unique_flags[ucount++] = i;
        }
    }
    *unique_count = ucount;
}


bool parse_module_filename(const char *filepath, module_info_t *modinfo) {
    const char *filename = strrchr(filepath, '\\');
    if (filename)
        filename++;
    else
        filename = filepath;


    const char *prefix = "sectioncache_";
    size_t prefix_len = strlen(prefix);
    if (strncmp(filename, prefix, prefix_len) != 0) {
        FATAL("Filename does not start with %s: %s\n", prefix, filename);
    }

    const char *rest = filename + prefix_len;
    const char *last_us = strrchr(rest, '_');
    if (!last_us) {
        FATAL("Failed to find last underscore in filename: %s\n", filename);
    }

    const char *second_last_us = NULL;
    const char *p = last_us;
    while (p > rest) {
        p--;
        if (*p == '_') {
            second_last_us = p;
            break;
        }
    }
    if (!second_last_us) {
        FATAL("Failed to find second underscore in filename: %s\n", filename);
    }

    size_t modname_len = second_last_us - rest;
    strncpy(modinfo->module_name, rest, modname_len);
    modinfo->module_name[modname_len] = '\0';

    char modbase_str[17] = {0};
    size_t modbase_len = last_us - (second_last_us + 1);
    if(modbase_len != 16){
        FATAL("Failed to parse module base address.\n");
    }
    strncpy(modbase_str, second_last_us + 1, modbase_len);
    modbase_str[modbase_len] = '\0';

    const char *dot = strchr(last_us, '.');
    if (!dot) {
        FATAL("Failed to find extension dot in filename: %s\n", filename);
    }
    
    char modsize_str[9] = {0};
    size_t modsize_len = dot - (last_us + 1);
    if(modsize_len != 8){
        FATAL("Failed to parse module size.\n");
    }
    strncpy(modsize_str, last_us + 1, modsize_len);
    modsize_str[modsize_len] = '\0';

    unsigned long long base = 0;
    unsigned int size = 0;
    if (sscanf(modbase_str, "%16llx", &base) != 1) {
        FATAL("Failed to parse base address from %s\n", modbase_str);
    }
    if (sscanf(modsize_str, "%8x", &size) != 1) {
        FATAL("Failed to parse size from %s\n", modsize_str);
    }

    modinfo->base = (void *)base;
    modinfo->size = (size_t)size;

    return true;
}


struct pt_image *prepare_pt_image(file_list *dat_files) {
    if (!dat_files) {
        FATAL("No .dat files\n");
    }

    section_cache = pt_iscache_alloc("winafl_cache");
    if (!section_cache) {
        FATAL("pt_iscache_alloc failed, GLE=%x.\n", GetLastError());
    }

    image = pt_image_alloc("winafl_image");
    if (!image) {
        FATAL("pt_image_alloc failed, GLE=%x.\n", GetLastError());
    }

    module_info_t *loaded_module;

    for (int i = 0; i < dat_files->count; i++) {
        loaded_module = (module_info_t *)malloc(sizeof(module_info_t));
        if (parse_module_filename(dat_files->files[i], loaded_module) == true) {
            loaded_module->isid = pt_iscache_add_file(section_cache, dat_files->files[i], 0, loaded_module->size, (uint64_t)loaded_module->base);
            if (loaded_module->isid < 0) {
                FATAL("Error adding file to pt cache.");
            }
            // printf("pt cache added for %s, isid=%d\n", loaded_module->module_name, loaded_module->isid);
            
            pt_image_add_cached(image, section_cache, loaded_module->isid, NULL);
            loaded_module->next = all_modules;
            all_modules = loaded_module;
        }
        else{
            FATAL("parse_module_filename Failed.\n");
        }
    }

    return image;
}

PIPT_TRACE_DATA get_pt_trace_data(const char* filename){
    PIPT_TRACE_DATA trace_data = NULL;
    FILE *fp = fopen(filename, "rb");
    if (!fp) {
        FATAL("Error opening file: %s, GLE=%x\n", filename, GetLastError());
    }

    fseek(fp, 0, SEEK_END);
    size_t file_size = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    trace_data = (PIPT_TRACE_DATA)HeapAlloc(GetProcessHeap(), HEAP_ZERO_MEMORY, file_size);
    if (!trace_data) {
        FATAL("Memory allocation failed for raw PT data copy, GLE=%x.\n", GetLastError());
    }
    
    size_t bytes_read = fread(trace_data, 1, file_size, fp);
    if (bytes_read != file_size) {
        FATAL("Error reading file: %s\n", filename);
    }
    
    fclose(fp);
    return trace_data;
}


void append_trace_data(unsigned char *trace_data, size_t append_size) {
    size_t space_left = TRACE_BUFFER_SIZE_DEFAULT - trace_size;

    if (!space_left) {
        FATAL("Warning: Trace buffer is full\n");
    }

    if (append_size > space_left) {
        append_size = space_left;
        fprintf(stderr, "Warning: Trace will be truncated\n");
    }

    if (append_size == 0) return;

    memcpy(trace_buffer + trace_size, trace_data, append_size);
    trace_size += append_size;
}

bool findpsb(unsigned char **data, size_t *size) {
    if (*size < 16) return false;

    if (memcmp(*data, psb, sizeof(psb)) == 0) return true;

    for (size_t i = 0; i < (*size - sizeof(psb) - 1); i++) {
        if (((*data)[i] == psb[0]) && ((*data)[i+1] == psb[1])) {
            if (memcmp((*data) + i, psb, sizeof(psb)) == 0) {
                *data = *data + i;
                *size = *size - i;
                return true;
            }
        }
    }

    return false;
}

bool collect_thread_trace(PIPT_TRACE_HEADER traceHeader) {
    // printf("ring offset: %u\n", traceHeader->RingBufferOffset);

    bool trace_buffer_overflow = false;
    trace_size = 0;

    unsigned char *trailing_data = traceHeader->Trace + traceHeader->RingBufferOffset;
    size_t trailing_size = traceHeader->TraceSize - traceHeader->RingBufferOffset;
    if (findpsb(&trailing_data, &trailing_size)) {
        trace_buffer_overflow = true;
        // printf("Warning: Trace buffer overflowed, trace will be truncated\n");
        append_trace_data(trailing_data, trailing_size);
    }

    append_trace_data(traceHeader->Trace, traceHeader->RingBufferOffset);

    return trace_buffer_overflow;
}

bool collect_trace(crash_info_t* crash, PIPT_TRACE_DATA pTraceData)
{
    bool trace_buffer_overflow = false;

    PIPT_TRACE_HEADER traceHeader;
    DWORD dwTraceSize;

    dwTraceSize = pTraceData->TraceSize;

    traceHeader = (PIPT_TRACE_HEADER)pTraceData->TraceData;

    while (dwTraceSize > (unsigned)(FIELD_OFFSET(IPT_TRACE_HEADER, Trace))) {
        if (traceHeader->ThreadId == crash->crash_thread_id) {
            trace_buffer_overflow = collect_thread_trace(traceHeader);
        }

        dwTraceSize -= (FIELD_OFFSET(IPT_TRACE_HEADER, Trace) + traceHeader->TraceSize);

        traceHeader = (PIPT_TRACE_HEADER)(traceHeader->Trace +
            traceHeader->TraceSize);
    }

    return trace_buffer_overflow;
}

bool add_image(pt_image *image, uint64_t ip){

    ULONG moduleIndex = 0;
    ULONG64 moduleBase = 0;
    HRESULT hr = g_DebugSymbols->GetModuleByOffset(ip, 0, &moduleIndex, &moduleBase);
    if (FAILED(hr)) {
        fprintf(stderr, "GetModuleByOffset failed for ip 0x%llx: 0x%08x\n", ip, hr);
        return false;
    }

    DEBUG_MODULE_PARAMETERS modParams = {0};
    modParams.Size = sizeof(modParams);
    hr = g_DebugSymbols->GetModuleParameters(1, &moduleBase, moduleIndex, &modParams);
    if (FAILED(hr)) {
        fprintf(stderr, "GetModuleParameters failed for module index %d: 0x%08x\n", moduleIndex, hr);
        return false;
    }

    char imageName[MAX_PATH] = {0};
    char moduleName[MAX_PATH] = {0};
    char loadedImageName[MAX_PATH] = {0};
    ULONG imageNameSize = 0, moduleNameSize = 0, loadedImageNameSize = 0;
    hr = g_DebugSymbols->GetModuleNames(moduleIndex, moduleBase,
        imageName, sizeof(imageName), &imageNameSize,
        moduleName, sizeof(moduleName), &moduleNameSize,
        loadedImageName, sizeof(loadedImageName), &loadedImageNameSize);
    if (FAILED(hr)) {
        fprintf(stderr, "GetModuleNames failed for module index %d: 0x%08x\n", moduleIndex, hr);
        return false;
    }

    // printf("Module: %s, Base: 0x%llx, Size: 0x%x\n", moduleName, moduleBase, modParams.Size);

    module_info_t *loaded_module = (module_info_t *)malloc(sizeof(module_info_t));
    strncpy(loaded_module->module_name, moduleName, MAX_PATH - 1);
    loaded_module->module_name[MAX_PATH - 1] = '\0';
    loaded_module->base = (void *)moduleBase;
    loaded_module->size = (size_t)modParams.Size;

    char tmpfilename[MAX_PATH] = {0};
    snprintf(tmpfilename, MAX_PATH, "%s\\ptmodules\\sectioncache_%s_%016llx_%08x.dat",
            out_dir, moduleName, moduleBase, modParams.Size);
    
    BYTE *modulebuf = (BYTE *)malloc(modParams.Size);
    ULONG bytesRead = 0;
    hr = g_DebugDataSpaces->ReadVirtual(moduleBase, modulebuf, modParams.Size, &bytesRead);
    g_DebugDataSpaces->Release();
    if (FAILED(hr) || bytesRead != modParams.Size) {
        fprintf(stderr, "ReadVirtual failed for module %s, bytesRead=%lu, expected=%u, hr=0x%08x\n", moduleName, bytesRead, modParams.Size, hr);
        free(modulebuf);
        free(loaded_module);
        return false;
    }

    FILE *fp = fopen(tmpfilename, "wb");
    if (!fp) {
        fprintf(stderr, "Error opening file for writing: %s\n", tmpfilename);
        free(modulebuf);
        free(loaded_module);
        return false;
    }
    fwrite(modulebuf, 1, modParams.Size, fp);
    fclose(fp);
    free(modulebuf);

    loaded_module->isid = pt_iscache_add_file(section_cache, tmpfilename, 0, modParams.Size, moduleBase);
    if (loaded_module->isid  <= 0) {
        fprintf(stderr, "Error adding file to pt cache for module %s\n", moduleName);
        free(loaded_module);
        return false;
    }
    pt_image_add_cached(image, section_cache, loaded_module->isid, NULL);
    loaded_module->next = all_modules;
    all_modules = loaded_module;

    return true;
}

void decode_trace_full_insn(unsigned char *pt_data, size_t pt_size, struct pt_image *image, uint64_t last_address, const char* output_filepath, const uint64_t target_start, const uint64_t target_end)
{   
    struct pt_insn_decoder *decoder;
    struct pt_config config;
    int status = 0;
    uint64_t syncOffset, offset;

    memset(&config, 0, sizeof(config));
    config.size = sizeof(config);
    
    pt_config_init(&config);
    pt_cpu_read(&config.cpu);
    pt_cpu_errata(&config.errata, &config.cpu);
    config.begin = pt_data;
    config.end = pt_data + pt_size;

    config.decode.callback = NULL;
    config.decode.context = NULL;


    decoder = pt_insn_alloc_decoder(&config);
    if (!decoder) {
        FATAL("Error allocating instruction decoder\n");
    }
    if (pt_insn_set_image(decoder, image) < 0) {
        FATAL("Error setting image for instruction decoder\n");
    }

    status = pt_insn_sync_forward(decoder);
    if (status < 0) {
        FATAL("Instruction decoder sync failed: %d\n", status);
    }

    pt_insn_get_sync_offset(decoder, &syncOffset);

    FILE *output_file = fopen(output_filepath, "w");
    if (!output_file) {
        FATAL("Failed to create %s\n", output_filepath);
    }
    
    fprintf(output_file, "Execution Trace Log:\n");
    fprintf(output_file, "-------------------------------------------\n");

    uint64_t pending_ip;
    bool has_pending_out = false;

    for (int i = 0;;i++) {
        while (status & pts_event_pending) {
            struct pt_event event;
            status = pt_insn_event(decoder, &event, sizeof(event));
            if (status < 0){
                break;
            }
            // printf("event %d\n", event.type);
        }

        struct pt_insn insn;
        memset(&insn, 0, sizeof(insn));
        pt_insn_get_offset(decoder, &offset);
        status = pt_insn_next(decoder, &insn, sizeof(insn));
        // printf("decoded status %d\n", status);
        if (status < 0){
            if(status == -pte_eos){
                // printf("Decoding Finished\n");
                break;
            }
            else if(status == -pte_nomap){
                if (add_image(image, insn.ip)) {
                    continue;
                }
                else{
                    status = pt_insn_sync_forward(decoder);
                    if (status < 0) {
                        break;
                    }
                }
            }
            else if (status == -pte_no_enable) {
                // printf("Error: tracing is not enabled (enabled event missing).\n");
                break;
            }
            else{
                FATAL("pt_insn_next failed: %d\n", status);
            }
        }
        if((insn.ip >= target_start) &&(insn.ip <= target_end)){
            
            if(has_pending_out){
                pending_ip = NULL;
                has_pending_out = false;
            }
            // fprintf(output_file, "[%d] status: %d\tip: %016llx\tsyncOffset: %d\toffset: %d\n", i, status, insn.ip, syncOffset, offset);
            PrintSymbolAndDisassembly(insn.ip, output_file);

        }
        else{
            if(!has_pending_out){
                pending_ip = insn.ip;
                has_pending_out = true;
            }
        }
    }
    
    if(has_pending_out){
        PrintSymbolAndDisassembly(pending_ip, output_file);
    }

    if((last_address >= target_start) &&(last_address <= target_end)){
        PrintSymbolAndDisassembly(last_address, output_file);
    }
    fprintf(output_file, "-------------------------------------------\n");

    fclose(output_file);
    pt_insn_free_decoder(decoder);
}


bool analyze_crash_ptlog(crash_info_t* crash, file_list *image_files, const char* analyze_dir){
    if(!image){
        image = prepare_pt_image(image_files);
    }

    PIPT_TRACE_DATA trace_data = get_pt_trace_data(crash->crash_ptlog_filename);
    bool trace_buffer_overflowed = collect_trace(crash, trace_data);
    printf("trace_buffer_overflowed: %s\n", trace_buffer_overflowed ? "YES" : "NO");
    if(trace_buffer_overflowed){
        printf("Warning: Trace buffer overflowed, trace will be truncated\n\n");
    }

    // trace_buffer = trace_data->TraceData;
    // trace_size = trace_data->TraceSize;

    HRESULT hr = InitializeDbgEng();
    hr = OpenDumpFileAndWait(crash->crash_procdump_filename);

    const char *base_name = strrchr(crash->crash_input_filename, '\\');
    if (!base_name) {
        FATAL("Failed to find base name of crash input: %s\n", crash->crash_input_filename);
    }
    base_name++;

    char full_trace[MAX_PATH], cov_trace[MAX_PATH], slice_path[MAX_PATH];
    snprintf(full_trace, MAX_PATH, "%s\\%s_full_execution_trace.txt", analyze_dir, base_name);
    snprintf(cov_trace,  MAX_PATH, "%s\\%s_coverage_trace.txt", analyze_dir, base_name);
    snprintf(slice_path, MAX_PATH, "%s\\%s_slice_for_root_cause_analysis.txt", analyze_dir, base_name);

    printf("[1] Decoding FULL execution trace...\n");
    decode_trace_full_insn((unsigned char*)trace_data, trace_size, image, crash->frames[0].address, full_trace, 0, UINT64_MAX);
    printf("\t -> Full trace saved: %s\n", full_trace);

    if(strlen(coverage_module) > 0){
        module_info_t *current = all_modules;
        while (current) {
            if(strcmp(current->module_name, coverage_module) == 0){
                break;
            }
            current = current->next;
        }
        printf("\n[2] Decoding COVERAGE-ONLY trace (module=%s)...\n", coverage_module);
        decode_trace_full_insn((unsigned char*)trace_data, trace_size, image, crash->frames[0].address, cov_trace, (uint64_t)current->base, (uint64_t)current->base + current->size);
        printf("\t-> Coverage trace saved: %s\n\n", cov_trace);

        printf("[3] Backward slice (root-cause seed)...\n");
        analyze_trace_file(cov_trace, coverage_module, slice_path, crash->mode == MODE_64);
        printf("\t-> Slice report: %s\n", slice_path);

        if (slice_list->count < MAX_FILES) {
            slice_list->files[slice_list->count] = _strdup(slice_path);
            slice_list->count++;
        } else {
            FATAL("Warning: Too many slice files, some will be ignored\n");
        }
    }
    
    g_DebugClient->EndSession(DEBUG_END_DISCONNECT);
    RELEASE(g_DebugSymbols);
    RELEASE(g_DebugControl);
    RELEASE(g_DebugClient);
    return true;
}
 
void print_usage(const char *prog) {
    printf(
        "Usage: %s <fuzz_output_folder> [-coverage_module <module.dll>] [-h|--help]\n\n"
        "Options:\n"
        "  -coverage_module <DLL>   Only decode instructions inside <DLL>'s address range\n"
        "  -h, --help               Show this help message and exit\n",
        prog
    );
}
 
int main(int argc, char** argv){


    if (argc == 2 && (strcmp(argv[1], "-h")==0 || strcmp(argv[1], "--help")==0)) {
        print_usage(argv[0]);
        return 0;
    }

    if (argc < 2) {
        printf("Usage: %s <fuzz_output_folder> [-coverage_module module.dll]\n", argv[0]);
        return 0;
    }

    out_dir = argv[1];
    parse_options(argc, (const char **)argv);

    char crash_dir[MAX_PATH];
    char image_dir[MAX_PATH];
    char analyze_dir[MAX_PATH];

    trace_buffer = (unsigned char *)malloc(TRACE_BUFFER_SIZE_DEFAULT);
    trace_size = 0;

    snprintf(crash_dir, sizeof(crash_dir), "%s\\crashes", out_dir);
    snprintf(image_dir, sizeof(image_dir), "%s\\ptmodules", out_dir);
    snprintf(analyze_dir, sizeof(analyze_dir), "%s\\analyze", out_dir);
    if (_mkdir(analyze_dir)) {
        FATAL("Unable to create '%s'", analyze_dir);
    }

    file_list *debug_files = get_file_list(crash_dir, "*debug.txt");
    file_list *image_files = get_file_list(image_dir, "*.dat");

    crash_info_t *crashes = (crash_info_t *)malloc(sizeof(crash_info_t) * debug_files->count);
    for(int i=0; i < debug_files->count; i++){
        if (parse_crash_debug_file(debug_files->files[i], &crashes[i]) !=0 ){
            FATAL("Failed to parse crash debug file.\n");
        }
    }
    
    int first_unique_indices[MAX_FILES];
    int first_unique_count = 0;
    remove_duplicate_crashes(crashes, debug_files->count, first_unique_indices, &first_unique_count);

    printf("=============================================================================================================================================\n");
    printf("+---------------------------------------------+\n");
    printf("|       WinAFL-PT Crash Analyzer v1.0         |\n");
    printf("|    Slice for Root-Cause Analysis Report     |\n");
    printf("+---------------------------------------------+\n");
    printf("Input folder            : %s\n", out_dir);
    printf("Total crashes           : %d\n", debug_files->count);
    printf("First Unique crashes    : %d\n", first_unique_count);
    printf("Coverage module         : %s\n", coverage_module[0] ? coverage_module : "None");
    printf("Output directory        : %s\n", analyze_dir);
    
    slice_list = (file_list *)malloc(sizeof(file_list));
    if (!slice_list) {
        FATAL("Memory allocation failed, GLE=%x\n", GetLastError());
    }
    
    slice_list->files = (char **)malloc(sizeof(char*) * MAX_FILES);
    if (!slice_list->files) {
        free(slice_list);
        FATAL("Memory allocation failed, GLE=%x\n", GetLastError());
    }
    slice_list->count = 0;

    for(int i = 0; i < first_unique_count; i++){
        crash_info_t *c = &crashes[first_unique_indices[i]];
        const char *base_name = strrchr(c->crash_input_filename, '\\') + 1;
        printf("=============================================================================================================================================\n");
        printf(">>> Crash #%d of %d: %s (ThreadID=0x%X) <<<\n\n", i+1, first_unique_count, base_name, c->crash_thread_id);
    
        analyze_crash_ptlog(&crashes[first_unique_indices[i]], image_files, analyze_dir);

    }

    int *second_unique_indices = (int *)malloc(sizeof(int) * slice_list->count);
    if (!second_unique_indices) {
        FATAL("Memory allocation failed, GLE=%x\n", GetLastError());
    }

    int second_unique_count = deduplicate_root_cause_seeds((const char **)slice_list->files, slice_list->count, second_unique_indices);
    printf("\n=============================================================================================================================================\n");
    printf("+----------------------------------------------- FINAL ROOT-CAUSE SEED REPORT ---------------------------------------------------+\n");
    printf("| Input folder            : %-100s |\n", out_dir);
    printf("| Total crashes analyzed  : %-100d |\n", debug_files->count);
    printf("| Phase 1 Unique crashes  : %-100d |\n", first_unique_count);
    printf("| Phase 2 Unique seeds    : %-100d |\n", second_unique_count);
    printf("| Output directory        : %-100s |\n", analyze_dir);
    printf("+-------------------------------------------------------------------------------------------------------------------------------+\n");
    for (int i = 0; i < second_unique_count; i++) {
        int idx = second_unique_indices[i];
        printf("| Seed #%2d: %-115s |\n", i+1, slice_list->files[idx]);
    }
    printf("+-------------------------------------------------------------------------------------------------------------------------------+\n");
    printf("=============================================================================================================================================\n");
    
    free(second_unique_indices);

    printf("\nAll analyses completed.\n");
    printf("Reports available under: %s\n", analyze_dir);

    free_file_list(slice_list);
    free_file_list(debug_files);
    free_file_list(image_files);
    free(crashes);
    free(trace_buffer);

    return 0;
}