#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include "common.h"

void build_memory_map(const char *reset_vec_addr, uint64_t dram_size) {
  assert(memory_map.empty());
  dram = new char[dram_size]{};
  // NOTE: keep the start addresses aligned to at least 4 KB (sizes don't have
  // to be round)
  memory_map = {
      MemoryMapEntry{0x1000, 0x1000, (void *)reset_vec_addr},
      MemoryMapEntry{0x80000000, dram_size, (void *)dram},
  };
}

void copy_to_physical_memory(const char *src, uint64_t start_addr,
                             uint64_t size) {
  uint64_t end_addr = start_addr + size;
  assert(end_addr > start_addr);

  for (auto &entry : memory_map) {
    if (entry.start <= start_addr && entry.start + entry.size > start_addr) {
      // don't cross memory map entries
      assert(entry.start + entry.size >= end_addr);

      char *dst = (char *)entry.ptr + (start_addr - entry.start);
      memcpy(dst, src, size);
      return;
    }
  }
  assert(false);
}

void *mmap_whole_file_ro(const char *filepath, uint64_t *filelen) {
  int fd = open(filepath, O_RDONLY);
  assert(fd >= 0);

  struct stat st;
  assert(fstat(fd, &st) != -1);
  *filelen = st.st_size;
  assert(*filelen > 0);

  char *data = (char *)mmap(nullptr, *filelen, PROT_READ, MAP_PRIVATE, fd, 0);
  assert(data != MAP_FAILED);

  close(fd);
  return data;
}

void load_elf_to_physical_memory(const char *filepath) {
  uint64_t filelen;
  char *data = (char *)mmap_whole_file_ro(filepath, &filelen);

  assert(filelen >= 64);

  uint64_t magic = *(uint64_t *)data;
  assert(magic == 0x00010102464c457ful); // little-endian 64-bit system v
  uint16_t e_type = *(uint16_t *)(data + 0x10);
  assert(e_type == 2); // executable
  uint16_t e_machine = *(uint16_t *)(data + 0x12);
  assert(e_machine == 243); // risc-v

  uint64_t e_phoff = *(uint64_t *)(data + 0x20);
  uint16_t e_phnum = *(uint16_t *)(data + 0x38);
  size_t ph_size = 0x38 * e_phnum;
  size_t ph_end = e_phoff + ph_size;
  assert(e_phoff % 8 == 0);
  assert(ph_end >= e_phoff);
  assert(ph_end < filelen);

  char *ph_end_p = data + ph_end;
  for (char *phent_p = data + e_phoff; phent_p != ph_end_p; phent_p += 0x38) {
    uint32_t p_type = *(uint32_t *)phent_p;
    if (p_type != 1 /* LOAD */)
      continue;

    uint64_t p_offset = *(uint64_t *)(phent_p + 0x8);
    uint64_t p_paddr = *(uint64_t *)(phent_p + 0x18);
    uint64_t p_filesz = *(uint64_t *)(phent_p + 0x20);
    uint64_t p_memsz = *(uint64_t *)(phent_p + 0x28);
    assert(p_filesz <= p_memsz);
    if (p_filesz == 0)
      continue;
    uint64_t file_seg_end = p_offset + p_filesz;
    assert(file_seg_end > p_offset && file_seg_end <= filelen);

    copy_to_physical_memory(data + p_offset, p_paddr, p_filesz);
  }

  munmap(data, filelen);
}

void load_fdt_to_physical_memory(const char *filepath, uint64_t addr) {
  uint64_t filelen;
  char *data = (char *)mmap_whole_file_ro(filepath, &filelen);

  assert(filelen >= 4);
  uint32_t magic = *(uint32_t *)data;
  assert(magic == 0xedfe0dd0);
  copy_to_physical_memory(data, addr, filelen);

  munmap(data, filelen);
}
