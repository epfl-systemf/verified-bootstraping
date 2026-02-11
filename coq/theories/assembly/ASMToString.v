From impboot Require Import assembly.ASMSyntax.
From impboot Require Import utils.Core.
Require Import impboot.utils.Words4Naive.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
From impboot Require Import imp2asm.ImpToASMCodegen.
From impboot Require Import commons.CompilerUtils.

Open Scope string.

(* This is named reg2str1, since when I named it reg2str1, it reified forever, see example in AsmToStringDerivations.v *)
Definition reg2str1 (r: reg) (str: string): string :=
  match r with
  | RAX =>
    let/d rs := "%rax" in
    let/d res := rs ++ str in
    res
  | RDI =>
    let/d rs := "%rdi" in
    let/d res := rs ++ str in
    res
  | RBX =>
    let/d rs := "%rbx" in
    let/d res := rs ++ str in
    res
  | RBP =>
    let/d rs := "%rbp" in
    let/d res := rs ++ str in
    res
  | R12 =>
    let/d rs := "%r12" in
    let/d res := rs ++ str in
    res
  | R13 =>
    let/d rs := "%r13" in
    let/d res := rs ++ str in
    res
  | R14 =>
    let/d rs := "%r14" in
    let/d res := rs ++ str in
    res
  | R15 =>
    let/d rs := "%r15" in
    let/d res := rs ++ str in
    res
  | RDX =>
    let/d rs := "%rdx" in
    let/d res := rs ++ str in
    res
  end.

Definition lab (n: nat) (str: string): string :=
  let/d num := num2str n str in
  let/d res := String "L" num in
  res.

Fixpoint clean (cs: string) (acc: string): string :=
  match cs with
  | EmptyString => acc
  | String c cs =>
    let/d n := nat_of_ascii c in
    if (n <? 43)%nat then
      let/d res := clean cs acc in
      res
    else
      let/d cl := clean cs acc in
      let/d res := String c cl in
      res
  end.

Notation "cst ::: s" :=
  ltac:(match cst with
        | context c[EmptyString] => let c' := context c[s] in exact c'
        | _ => fail "Left string is not constant"
        end) (at level 60, only parsing).

Definition inst2str_const (r: reg) (imm: word64) (str: string): string :=
  let/d imm_n := Z.to_N (word.unsigned imm) in
  let/d reg_str := reg2str1 r str in
  let/d comma_reg := ", " ::: reg_str in
  let/d imm_str := N2str imm_n comma_reg in
  let/d res := "movq $" ::: imm_str in
  res.

Definition inst2str_mov (dst: reg) (src: reg) (str: string): string :=
  let/d dst_str := reg2str1 dst str in
  let/d comma_dst := ", " ::: dst_str in
  let/d src_comma_dst := reg2str1 src  comma_dst in
  let/d res := "movq " ::: src_comma_dst in
  res.

Definition inst2str_add (dst: reg) (src: reg) (str: string): string :=
  let/d dst_str := reg2str1 dst str in
  let/d comma_dst := ", " ::: dst_str in
  let/d src_comma_dst := reg2str1 src comma_dst in
  let/d res := "addq " ::: src_comma_dst in
  res.

Definition inst2str_sub (dst: reg) (src: reg) (str: string): string :=
  let/d dst_str := reg2str1 dst str in
  let/d comma_dst := ", " ::: dst_str in
  let/d src_comma_dst := reg2str1 src comma_dst in
  let/d res := "subq " ::: src_comma_dst in
  res.

Definition inst2str_div (r: reg) (str: string): string :=
  let/d r_str := reg2str1 r str in
  let/d res := "divq " ::: r_str in
  res.

Definition inst2str_jump_always (n: nat) (str: string): string :=
  let/d lab_str := lab n str in
  let/d res := "jmp " ::: lab_str in
  res.

Definition inst2str_jump_equal (r1: reg) (r2: reg) (n: nat) (str: string): string :=
  let/d cmpq_prefix := "cmpq " in
  let/d je_prefix := " ; je " in
  let/d lab_str := lab n str in
  let/d je_lab := je_prefix ++ lab_str in
  let/d r1_str := reg2str1 r1 je_lab in
  let/d comma_r1 := ", " ::: r1_str in
  let/d r2_comma_r1 := reg2str1 r2 comma_r1 in
  let/d res := cmpq_prefix ++ r2_comma_r1 in
  res.

Definition inst2str_jump_less (r1: reg) (r2: reg) (n: nat) (str: string): string :=
  let/d cmpq_prefix := "cmpq " in
  let/d jb_prefix := " ; jb " in
  let/d lab_str := lab n str in
  let/d jb_lab := jb_prefix ++ lab_str in
  let/d r1_str := reg2str1 r1 jb_lab in
  let/d comma_r1 := ", " ::: r1_str in
  let/d r2_comma_r1 := reg2str1 r2 comma_r1 in
  let/d res := cmpq_prefix ++ r2_comma_r1 in
  res.

Definition inst2str_call (n: nat) (str: string): string :=
  let/d lab_str := lab n str in
  let/d res := "call " ::: lab_str in
  res.

Definition inst2str_ret (str: string): string :=
  let/d res := "ret" ::: str in
  res.

Definition inst2str_pop (r: reg) (str: string): string :=
  let/d r_str := reg2str1 r str in
  let/d res := "popq " ::: r_str in
  res.

Definition inst2str_push (r: reg) (str: string): string :=
  let/d r_str := reg2str1 r str in
  let/d res := "pushq " ::: r_str in
  res.

Definition inst2str_load_rsp (r: reg) (n: nat) (str: string): string :=
  let/d mult_const := 8 in
  let/d offset := mult_const * n in
  let/d rsp_prefix := "(%rsp), " in
  let/d r_str := reg2str1 r str in
  let/d rsp_r := rsp_prefix ++ r_str in
  let/d offset_str := num2str offset rsp_r in
  let/d res := "movq " ::: offset_str in
  res.

Definition inst2str_store_rsp (r: reg) (n: nat) (str: string): string :=
  let/d mult_const := 8 in
  let/d offset := mult_const * n in
  let/d rsp_suffix := "(%rsp), " in
  let/d rsp_suffix_str := rsp_suffix ++ str in
  let/d offset_str := num2str offset rsp_suffix_str in
  let/d comma_offset := ", " ::: offset_str in
  let/d r_str := reg2str1 r comma_offset in
  let/d res := "movq " ::: r_str in
  res.

Definition inst2str_add_rsp (n: nat) (str: string): string :=
  let/d mult_const := 8 in
  let/d offset := mult_const * n in
  let/d rsp_suffix := ", %rsp" in
  let/d rsp_suffix_str := rsp_suffix ++ str in
  let/d offset_str := num2str offset rsp_suffix_str in
  let/d res := "addq $" ::: offset_str in
  res.

Definition inst2str_sub_rsp (n: nat) (str: string): string :=
  let/d mult_const := 8 in
  let/d offset := mult_const * n in
  let/d rsp_suffix := ", %rsp" in
  let/d rsp_suffix_str := rsp_suffix ++ str in
  let/d offset_str := num2str offset rsp_suffix_str in
  let/d res := "subq $" ::: offset_str in
  res.

Definition inst2str_store (src: reg) (a: reg) (w: word4) (str: string): string :=
  let/d w_n := Z.to_N (word.unsigned w) in
  let/d paren_close_str := ")" ::: str in
  let/d a_str := reg2str1 a paren_close_str in
  let/d paren_a := "(" ::: a_str in
  let/d w_str := N2str w_n paren_a in
  let/d comma_w := ", " ::: w_str in
  let/d src_comma_w := reg2str1 src comma_w in
  let/d res := "movq " ::: src_comma_w in
  res.

Definition inst2str_load (dst: reg) (a: reg) (w: word4) (str: string): string :=
  let/d w_n := Z.to_N (word.unsigned w) in
  let/d dst_str := reg2str1 dst str in
  let/d paren_close_dst := "), " ::: dst_str in
  let/d a_str := reg2str1 a paren_close_dst in
  let/d paren_a := "(" ::: a_str in
  let/d w_str := N2str w_n paren_a in
  let/d res := "movq " ::: w_str in
  res.

Definition inst2str_getchar1 (str: string): string :=
  let/d res := "movq stdin(%rip), %rdi ; call _IO_getc@PLT" ::: str in
  res.

Definition inst2str_putchar (str: string): string :=
  let/d res := "movq stdout(%rip), %rsi ; call _IO_putc@PLT" ::: str in
  res.

(* TODO: Auto ++ to ::: *)

Definition inst2str_exit (str: string): string :=
  let/d res := "call exit@PLT" ::: str in
  res.

Definition inst2str_comment (c: string) (str: string): string :=
  let/d suffix_str := " */" ::: str in
  let/d clean_c := clean c suffix_str in
  let/d res := "
  
  	/* " ::: clean_c in
  res.

Definition inst2str (i: instr) (str: string): string :=
  match i with
  | Const r imm =>
    let/d res := inst2str_const r imm str in
    res
  | Mov dst src =>
    let/d res := inst2str_mov dst src str in
    res
  | ASMSyntax.Add dst src =>
    let/d res := inst2str_add dst src str in
    res
  | Sub dst src =>
    let/d res := inst2str_sub dst src str in
    res
  | Div r =>
    let/d res := inst2str_div r str in
    res
  | Jump cond n =>
    match cond with
    | Always =>
      let/d res := inst2str_jump_always n str in
      res
    | Equal r1 r2 =>
      let/d res := inst2str_jump_equal r1 r2 n str in
      res
    | Less r1 r2 =>
      let/d res := inst2str_jump_less r1 r2 n str in
      res
    end
  | Call n =>
    let/d res := inst2str_call n str in
    res
  | Ret =>
    let/d res := inst2str_ret str in
    res
  | Pop r =>
    let/d res := inst2str_pop r str in
    res
  | Push r =>
    let/d res := inst2str_push r str in
    res
  | Load_RSP r n =>
    let/d res := inst2str_load_rsp r n str in
    res
  | StoreRSP r n =>
    let/d res := inst2str_store_rsp r n str in
    res
  | Add_RSP n =>
    let/d res := inst2str_add_rsp n str in
    res
  | Sub_RSP n =>
    let/d res := inst2str_sub_rsp n str in
    res
  | Store src a w =>
    let/d res := inst2str_store src a w str in
    res
  | Load dst a w =>
    let/d res := inst2str_load dst a w str in
    res
  | GetChar =>
    let/d res := inst2str_getchar1 str in
    res
  | PutChar =>
    let/d res := inst2str_putchar str in
    res
  | Exit =>
    let/d res := inst2str_exit str in
    res
  | Comment c =>
    let/d res := inst2str_comment c str in
    res
  end.


Fixpoint instrs2str (n: nat) (is: asm): string :=
  match is with
  | [] =>
    let/d res := EmptyString in
    res
  | i :: is =>
    let/d colon := ":"%char in
    let/d tab_char := "009"%char in
    let/d newline_char := "010"%char in
    let/d next_n := n + 1 in
    let/d rest_str := instrs2str next_n is in
    let/d newline_rest := String newline_char rest_str in
    let/d inst_str := inst2str i newline_rest in
    let/d tab_inst := String tab_char inst_str in
    let/d colon_tab_inst := String colon tab_inst in
    let/d result := lab n colon_tab_inst in
    result
  end.

Fixpoint concat_strings (ss: list string): string :=
  match ss with
  | [] =>
    let/d res := EmptyString in
    res
  | s :: ss =>
    let/d rest := concat_strings ss in
    let/d res := s ++ rest in
    res
  end.

Definition asm2str_header1: list string :=
  let/d bss_str := "	.bss
  " in
  let/d p2align1_str := "	.p2align 3            /* 8-byte align        */
  " in
  let/d heaps_lbl := "heapS:
  " in
  let/d space_str := "	.space 8*1024*1024  /* bytes of heap space */
  " in
  let/d list1 := [bss_str; p2align1_str; heaps_lbl; space_str] in
  list1.

Definition asm2str_header2: list string :=
  let/d p2align2 := "	.p2align 3            /* 8-byte align        */
  " in
  let/d heapE := "heapE:
    
  " in
  let/d dot_text := "	.text
  " in
  let/d globl := "	.globl main
  " in
  let/d list2 := [p2align2; heapE; dot_text; globl] in
  list2.

Definition asm2str_header3: list string :=
let/d main_colon := "main:
  " in
  let/d subq_str := "	subq $8, %rsp        /* 16-byte align %rsp */
  " in
  let/d movabs1_str := "	movabs $heapS, %r14  /* r14 := heap start  */
  " in
  let/d movabs2_str := "	movabs $heapE, %r15  /* r14 := heap end    */
  
    
    " in
  let/d list3 := [main_colon; subq_str; movabs1_str; movabs2_str] in
  list3.

Definition asm2str (is: asm): string :=
  let/d zero_val := 0 in
  let/d instrs_str := instrs2str zero_val is in
  let/d res := "	.bss
  	.p2align 3            /* 8-byte align        */
  heapS:
  	.space 8*1024*1024  /* bytes of heap space */
  	.p2align 3            /* 8-byte align        */
  heapE:
    
  	.text
  	.globl main
  main:
  	subq $8, %rsp        /* 16-byte align %rsp */
  	movabs $heapS, %r14  /* r14 := heap start  */
  	movabs $heapE, %r15  /* r14 := heap end    */
  
    
    " ::: instrs_str in
  res.
