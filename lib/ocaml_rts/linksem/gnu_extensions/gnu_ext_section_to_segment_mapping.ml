(*Generated by Lem from gnu_extensions/gnu_ext_section_to_segment_mapping.lem.*)
(** [gnu_ext_section_to_segment_mapping] contains (GNU specific) functionality
  * relating to calculating the section to segment mapping for an ELF file.  In
  * particular, the test over whether a section is inside a segment is ABI
  * specific.  This module provides that test.
  *)

open Lem_basic_classes
open Lem_bool
open Lem_num

open Elf_header
open Elf_program_header_table
open Elf_section_header_table
open Elf_types_native_uint

open Lem_string
open Show

open Gnu_ext_program_header_table

(** [elf32_section_in_segment sec_hdr segment] implements the
  * ELF_SECTION_IN_SEGMENT1 macro from readelf.  Note the macro is always used
  * with [check_vma] and [strict] set to 1.
  *
  #define ELF_SECTION_IN_SEGMENT_1(sec_hdr, segment, check_vma, strict)	\
  ((/* Only PT_LOAD, PT_GNU_RELRO and PT_TLS segments can contain	\
       SHF_TLS sections.  */						\
    ((((sec_hdr)->sh_flags & SHF_TLS) != 0)				\
     && ((segment)->p_type == PT_TLS					\
	 || (segment)->p_type == PT_GNU_RELRO				\
	 || (segment)->p_type == PT_LOAD))				\
    /* PT_TLS segment contains only SHF_TLS sections, PT_PHDR no	\
       sections at all.  */						\
    || (((sec_hdr)->sh_flags & SHF_TLS) == 0				\
	&& (segment)->p_type != PT_TLS					\
	&& (segment)->p_type != PT_PHDR))				\
   /* PT_LOAD and similar segments only have SHF_ALLOC sections.  */	\
   && !(((sec_hdr)->sh_flags & SHF_ALLOC) == 0				\
	&& ((segment)->p_type == PT_LOAD				\
	    || (segment)->p_type == PT_DYNAMIC				\
	    || (segment)->p_type == PT_GNU_EH_FRAME			\
	    || (segment)->p_type == PT_GNU_RELRO			\
	    || (segment)->p_type == PT_GNU_STACK))			\
   /* Any section besides one of type SHT_NOBITS must have file		\
      offsets within the segment.  */					\
   && ((sec_hdr)->sh_type == SHT_NOBITS					\
       || ((bfd_vma) (sec_hdr)->sh_offset >= (segment)->p_offset	\
	   && (!(strict)						\
	       || ((sec_hdr)->sh_offset - (segment)->p_offset		\
		   <= (segment)->p_filesz - 1))				\
	   && (((sec_hdr)->sh_offset - (segment)->p_offset		\
		+ ELF_SECTION_SIZE(sec_hdr, segment))			\
	       <= (segment)->p_filesz)))				\
   /* SHF_ALLOC sections must have VMAs within the segment.  */		\
   && (!(check_vma)							\
       || ((sec_hdr)->sh_flags & SHF_ALLOC) == 0			\
       || ((sec_hdr)->sh_addr >= (segment)->p_vaddr			\
	   && (!(strict)						\
	       || ((sec_hdr)->sh_addr - (segment)->p_vaddr		\
		   <= (segment)->p_memsz - 1))				\
	   && (((sec_hdr)->sh_addr - (segment)->p_vaddr			\
		+ ELF_SECTION_SIZE(sec_hdr, segment))			\
	       <= (segment)->p_memsz)))					\
   /* No zero size sections at start or end of PT_DYNAMIC.  */		\
   && ((segment)->p_type != PT_DYNAMIC					\
       || (sec_hdr)->sh_size != 0					\
       || (segment)->p_memsz == 0					\
       || (((sec_hdr)->sh_type == SHT_NOBITS				\
	    || ((bfd_vma) (sec_hdr)->sh_offset > (segment)->p_offset	\
	        && ((sec_hdr)->sh_offset - (segment)->p_offset		\
		    < (segment)->p_filesz)))				\
	   && (((sec_hdr)->sh_flags & SHF_ALLOC) == 0			\
	       || ((sec_hdr)->sh_addr > (segment)->p_vaddr		\
		   && ((sec_hdr)->sh_addr - (segment)->p_vaddr		\
		       < (segment)->p_memsz))))))
  *
  * From [internal.h] of readelf's source code.
  *)
  
(*val elf32_section_flags : elf32_section_header_table_entry -> natural -> bool*)
let elf32_section_flags0 sec_hdr typ:bool=  (not ((Uint32.logand sec_hdr.elf32_sh_flags (Uint32.of_string (Nat_big_num.to_string typ))) = (Uint32.of_string (Nat_big_num.to_string (Nat_big_num.of_int 0)))))
    
(*val elf64_section_flags : elf64_section_header_table_entry -> natural -> bool*)
let elf64_section_flags0 sec_hdr typ:bool=  (not ((Uint64.logand sec_hdr.elf64_sh_flags (Uint64.of_string (Nat_big_num.to_string typ))) = (Uint64.of_string (Nat_big_num.to_string (Nat_big_num.of_int 0)))))
    
(*val elf32_section_of_type : elf32_section_header_table_entry -> natural -> bool*)
let elf32_section_of_type sec_hdr typ:bool=  
 (sec_hdr.elf32_sh_type = Uint32.of_string (Nat_big_num.to_string typ))
  
(*val elf64_section_of_type : elf64_section_header_table_entry -> natural -> bool*)
let elf64_section_of_type sec_hdr typ:bool=  
 (sec_hdr.elf64_sh_type = Uint32.of_string (Nat_big_num.to_string typ))
  
(*val elf32_segment_of_type : elf32_program_header_table_entry -> natural -> bool*)
let elf32_segment_of_type segment typ:bool=  
 (segment.elf32_p_type = Uint32.of_string (Nat_big_num.to_string typ))
  
(*val elf64_segment_of_type : elf64_program_header_table_entry -> natural -> bool*)
let elf64_segment_of_type segment typ:bool=  
 (segment.elf64_p_type = Uint32.of_string (Nat_big_num.to_string typ))

(** Only PT_LOAD, PT_GNU_RELRO and PT_TLS segments can contain SHF_TLS sections
  * and PT_TLS segment contains only SHF_TLS sections, PT_PHDR no	sections at all
  *)
(*val elf32_section_in_segment1 : elf32_section_header_table_entry -> elf32_program_header_table_entry -> bool*)
let elf32_section_in_segment1 sec_hdr segment:bool=  
 ((elf32_section_flags0 sec_hdr shf_tls &&
  (elf32_segment_of_type segment elf_pt_tls ||    
(elf32_segment_of_type segment elf_pt_gnu_relro ||
    elf32_segment_of_type segment elf_pt_load))) ||
  (not (elf32_section_flags0 sec_hdr shf_tls)
  && (not (elf32_segment_of_type segment elf_pt_tls)
  && not (elf32_segment_of_type segment elf_pt_phdr))))
  
(*val elf64_section_in_segment1 : elf64_section_header_table_entry -> elf64_program_header_table_entry -> bool*)
let elf64_section_in_segment1 sec_hdr segment:bool=  
 ((elf64_section_flags0 sec_hdr shf_tls &&
  (elf64_segment_of_type segment elf_pt_tls ||    
(elf64_segment_of_type segment elf_pt_gnu_relro ||
    elf64_segment_of_type segment elf_pt_load))) ||
  (not (elf64_section_flags0 sec_hdr shf_tls)
  && (not (elf64_segment_of_type segment elf_pt_tls)
  && not (elf64_segment_of_type segment elf_pt_phdr))))

(** PT_LOAD and similar segments only have SHF_ALLOC sections *)

(*val elf32_section_in_segment2 : elf32_section_header_table_entry -> elf32_program_header_table_entry -> bool*)
let elf32_section_in_segment2 sec_hdr segment:bool=  
 (not ((not (elf32_section_flags0 sec_hdr shf_alloc)) &&
       (elf32_segment_of_type segment elf_pt_load ||        
(elf32_segment_of_type segment elf_pt_dynamic ||        
(elf32_segment_of_type segment elf_pt_gnu_eh_frame ||        
(elf32_segment_of_type segment elf_pt_gnu_relro ||
        elf32_segment_of_type segment elf_pt_gnu_stack))))))

(*val elf64_section_in_segment2 : elf64_section_header_table_entry -> elf64_program_header_table_entry -> bool*)
let elf64_section_in_segment2 sec_hdr segment:bool=  
 (not ((not (elf64_section_flags0 sec_hdr shf_alloc)) &&
       (elf64_segment_of_type segment elf_pt_load ||        
(elf64_segment_of_type segment elf_pt_dynamic ||        
(elf64_segment_of_type segment elf_pt_gnu_eh_frame ||        
(elf64_segment_of_type segment elf_pt_gnu_relro ||
        elf64_segment_of_type segment elf_pt_gnu_stack))))))
 
    
(** Any section besides one of type SHT_NOBITS must have file offsets within
  * the segment.
  *)

(*val elf32_sect_size : elf32_header -> elf32_section_header_table_entry -> elf32_program_header_table_entry -> natural*)
let elf32_sect_size hdr sec_hdr segment:Nat_big_num.num=  
 (if is_elf32_tbss_special sec_hdr segment then Nat_big_num.of_int 0
  else
    Nat_big_num.of_string (Uint32.to_string (hdr.elf32_shentsize)))
  
(*val elf64_sect_size : elf64_header -> elf64_section_header_table_entry -> elf64_program_header_table_entry -> natural*)
let elf64_sect_size hdr sec_hdr segment:Nat_big_num.num=  
 (if is_elf64_tbss_special sec_hdr segment then Nat_big_num.of_int 0
  else
    Nat_big_num.of_string (Uint32.to_string (hdr.elf64_shentsize)))
    
(*val elf32_section_in_segment3 : elf32_header -> elf32_section_header_table_entry -> elf32_program_header_table_entry -> bool*)
let elf32_section_in_segment3 hdr sec_hdr segment:bool=  
 (let sec_off = ((Nat_big_num.of_string (Uint32.to_string sec_hdr.elf32_sh_offset))) in
  let seg_off = ((Nat_big_num.of_string (Uint32.to_string segment.elf32_p_offset))) in
  let seg_fsz = ((Nat_big_num.of_string (Uint32.to_string segment.elf32_p_filesz))) in
  let sec_siz = ((elf32_sect_size hdr sec_hdr segment)) in
    elf32_section_of_type sec_hdr sht_nobits ||
    ( Nat_big_num.greater_equal sec_off seg_off &&    
(( Nat_big_num.less_equal( Nat_big_num.sub sec_off seg_off) ( Nat_big_num.sub seg_fsz(Nat_big_num.of_int 1))) &&
    ( Nat_big_num.less_equal (Nat_big_num.sub sec_off ( Nat_big_num.add seg_off sec_siz)) seg_fsz))))
  
(*val elf64_section_in_segment3 : elf64_header -> elf64_section_header_table_entry -> elf64_program_header_table_entry -> bool*)
let elf64_section_in_segment3 hdr sec_hdr segment:bool=  
 (let sec_off = ((Nat_big_num.of_string (Uint64.to_string sec_hdr.elf64_sh_offset))) in
  let seg_off = ((Nat_big_num.of_string (Uint64.to_string segment.elf64_p_offset))) in
  let seg_fsz = ((Ml_bindings.nat_big_num_of_uint64 segment.elf64_p_filesz)) in
  let sec_siz = ((elf64_sect_size hdr sec_hdr segment)) in
    elf64_section_of_type sec_hdr sht_nobits ||
    ( Nat_big_num.greater_equal sec_off seg_off &&    
(( Nat_big_num.less_equal( Nat_big_num.sub sec_off seg_off) ( Nat_big_num.sub seg_fsz(Nat_big_num.of_int 1))) &&
    ( Nat_big_num.less_equal (Nat_big_num.sub sec_off ( Nat_big_num.add seg_off sec_siz)) seg_fsz))))
      
(** SHF_ALLOC sections must have VMAs within the segment
  *)
  
(*val elf32_section_in_segment4 : elf32_header -> elf32_section_header_table_entry -> elf32_program_header_table_entry -> bool*)
let elf32_section_in_segment4 hdr sec_hdr segment:bool=  
 (let sec_addr = ((Nat_big_num.of_string (Uint32.to_string sec_hdr.elf32_sh_addr))) in
  let seg_vadr = ((Nat_big_num.of_string (Uint32.to_string segment.elf32_p_vaddr))) in
  let seg_mmsz = ((Nat_big_num.of_string (Uint32.to_string segment.elf32_p_memsz))) in
  let sec_size = ((elf32_sect_size hdr sec_hdr segment)) in
    (not (elf32_section_flags0 sec_hdr shf_alloc) || Nat_big_num.greater_equal
     sec_addr seg_vadr) && (Nat_big_num.less_equal (Nat_big_num.sub
     sec_addr seg_vadr) (Nat_big_num.sub seg_mmsz(Nat_big_num.of_int 1)) && Nat_big_num.less_equal (Nat_big_num.sub
     sec_addr ( Nat_big_num.add seg_vadr sec_size)) seg_mmsz))
  
(*val elf64_section_in_segment4 : elf64_header -> elf64_section_header_table_entry -> elf64_program_header_table_entry -> bool*)
let elf64_section_in_segment4 hdr sec_hdr segment:bool=  
 (let sec_addr = ((Ml_bindings.nat_big_num_of_uint64 sec_hdr.elf64_sh_addr)) in
  let seg_vadr = ((Ml_bindings.nat_big_num_of_uint64 segment.elf64_p_vaddr)) in
  let seg_mmsz = ((Ml_bindings.nat_big_num_of_uint64 segment.elf64_p_memsz)) in
  let sec_size = ((elf64_sect_size hdr sec_hdr segment)) in
     (not (elf64_section_flags0 sec_hdr shf_alloc) || Nat_big_num.greater_equal
     sec_addr seg_vadr) && (Nat_big_num.less_equal (Nat_big_num.sub
     sec_addr seg_vadr) (Nat_big_num.sub seg_mmsz(Nat_big_num.of_int 1)) && Nat_big_num.less_equal (Nat_big_num.sub
     sec_addr ( Nat_big_num.add seg_vadr sec_size)) seg_mmsz))
    
(** No zero size sections at start or end of PT_DYNAMIC *)

(*val elf32_section_in_segment5 : elf32_section_header_table_entry -> elf32_program_header_table_entry -> bool*)
let elf32_section_in_segment5 sec_hdr segment:bool=  
 (let sec_siz = ((Nat_big_num.of_string (Uint32.to_string sec_hdr.elf32_sh_size))) in
  let seg_msz = ((Nat_big_num.of_string (Uint32.to_string segment.elf32_p_memsz))) in
  let sec_off = ((Nat_big_num.of_string (Uint32.to_string sec_hdr.elf32_sh_offset))) in
  let seg_off = ((Nat_big_num.of_string (Uint32.to_string segment.elf32_p_offset))) in
  let seg_fsz = ((Nat_big_num.of_string (Uint32.to_string segment.elf32_p_filesz))) in
  let sec_adr = ((Nat_big_num.of_string (Uint32.to_string sec_hdr.elf32_sh_addr))) in
  let seg_vad = ((Nat_big_num.of_string (Uint32.to_string segment.elf32_p_vaddr))) in
    (not (elf32_segment_of_type segment elf_pt_dynamic)) || (not (Nat_big_num.equal sec_siz(Nat_big_num.of_int 0)) || (Nat_big_num.equal
    seg_msz(Nat_big_num.of_int 0) ||
    ((elf32_section_of_type sec_hdr sht_nobits ||
      ( Nat_big_num.greater sec_off seg_off && Nat_big_num.less (Nat_big_num.sub
       sec_off seg_off) seg_fsz)) &&
       (not (elf32_section_flags0 sec_hdr shf_alloc) ||
        ( Nat_big_num.greater sec_adr seg_vad && Nat_big_num.less (Nat_big_num.sub
         sec_adr seg_vad) seg_msz))))))

(*val elf64_section_in_segment5 : elf64_section_header_table_entry -> elf64_program_header_table_entry -> bool*)
let elf64_section_in_segment5 sec_hdr segment:bool=  
 (let sec_siz = ((Ml_bindings.nat_big_num_of_uint64 sec_hdr.elf64_sh_size)) in
  let seg_msz = ((Ml_bindings.nat_big_num_of_uint64 segment.elf64_p_memsz)) in
  let sec_off = ((Nat_big_num.of_string (Uint64.to_string sec_hdr.elf64_sh_offset))) in
  let seg_off = ((Nat_big_num.of_string (Uint64.to_string segment.elf64_p_offset))) in
  let seg_fsz = ((Ml_bindings.nat_big_num_of_uint64 segment.elf64_p_filesz)) in
  let sec_adr = ((Ml_bindings.nat_big_num_of_uint64 sec_hdr.elf64_sh_addr)) in
  let seg_vad = ((Ml_bindings.nat_big_num_of_uint64 segment.elf64_p_vaddr)) in
    (not (elf64_segment_of_type segment elf_pt_dynamic)) || (not (Nat_big_num.equal sec_siz(Nat_big_num.of_int 0)) || (Nat_big_num.equal
    seg_msz(Nat_big_num.of_int 0) ||
    ((elf64_section_of_type sec_hdr sht_nobits ||
      ( Nat_big_num.greater sec_off seg_off && Nat_big_num.less (Nat_big_num.sub
       sec_off seg_off) seg_fsz)) &&
       (not (elf64_section_flags0 sec_hdr shf_alloc) ||
        ( Nat_big_num.greater sec_adr seg_vad && Nat_big_num.less (Nat_big_num.sub
         sec_adr seg_vad) seg_msz))))))

(** The final section in segment tests, bringing all the above together.
  *)

(*val elf32_section_in_segment : elf32_header -> elf32_section_header_table_entry -> elf32_program_header_table_entry -> bool*)
let elf32_section_in_segment hdr sec_hdr segment:bool=  
 (elf32_section_in_segment1 sec_hdr segment &&  
(elf32_section_in_segment2 sec_hdr segment &&  
(elf32_section_in_segment3 hdr sec_hdr segment &&  
(elf32_section_in_segment4 hdr sec_hdr segment &&
  elf32_section_in_segment5 sec_hdr segment))))
    
(*val elf64_section_in_segment : elf64_header -> elf64_section_header_table_entry -> elf64_program_header_table_entry -> bool*)
let elf64_section_in_segment hdr sec_hdr segment:bool=  
 (elf64_section_in_segment1 sec_hdr segment &&  
(elf64_section_in_segment2 sec_hdr segment &&  
(elf64_section_in_segment3 hdr sec_hdr segment &&  
(elf64_section_in_segment4 hdr sec_hdr segment &&
  elf64_section_in_segment5 sec_hdr segment))))