.intel_syntax noprefix
.text
.globl copy_bytes
.type copy_bytes, @function
copy_bytes:
  push rbp
  mov rbp, rsp
  sub rsp, 32
  mov [rbp - 16], rbx
  mov [rbp - 24], r12
  mov r8, rdx
  mov r11, rdi
  mov rdi, rsi
  mov rsi, r11
.Lb0_0:
  mov r11, 0
  mov r9, r11
  mov r11, 1
  mov r10, r11
  mov r11, r9
  mov r9, r8
  mov r8, rdi
  mov rdi, rsi
  mov rsi, r11
  jmp .Lb0_1
.Lb0_1:
  mov r11, rsi
  mov rax, r9
  cmp r11, rax
  setge al
  movzx eax, al
  mov rbx, rax
  mov r11, rbx
  test r11, r11
  je .Lx0_1
  jmp .Lb0_3
.Lx0_1:
  jmp .Lb0_2
.Lb0_2:
  mov r11, r8
  mov rax, rsi
  add r11, rax
  mov rbx, r11
  mov rax, rbx
  movzx r11d, BYTE PTR [rax]
  mov r12, r11
  mov r11, rdi
  mov rax, rsi
  add r11, rax
  mov rbx, r11
  mov rax, rbx
  mov r11, r12
  mov [rax], r11b
  mov r11, rsi
  add r11, r10
  mov rbx, r11
  mov rsi, rbx
  jmp .Lb0_1
.Lb0_3:
  mov rbx, [rbp - 16]
  mov r12, [rbp - 24]
  leave
  ret
.size copy_bytes, .-copy_bytes
.globl put_u8
.type put_u8, @function
put_u8:
  push rbp
  mov rbp, rsp
  sub rsp, 80
  mov [rbp - 16], rbx
  mov [rbp - 24], r12
  mov [rbp - 32], r13
  mov [rbp - 40], r14
  mov [rbp - 48], r15
  mov r8, rdx
  mov r11, rdi
  mov rdi, rsi
  mov rsi, r11
.Lb1_0:
  mov r11, 100
  mov r9, r11
  mov r11, 10
  mov r10, r11
  mov r11, 48
  mov rbx, r11
  mov r11, 1
  mov r12, r11
  mov r11, 2
  mov r13, r11
  mov r11, 3
  mov r14, r11
  mov r11, r8
  mov rax, r9
  cmp r11, rax
  setge al
  movzx eax, al
  mov r15, rax
  mov r11, r15
  test r11, r11
  je .Lx1_1
  jmp .Lb1_1
.Lx1_1:
  jmp .Lb1_2
.Lb1_1:
  mov rax, r8
  mov rcx, r9
  test rcx, rcx
  jne .Lx1_2
  xor r11d, r11d
  jmp .Lx1_3
.Lx1_2:
  cmp rcx, -1
  jne .Lx1_4
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx1_4
  mov r11, rax
  jmp .Lx1_3
.Lx1_4:
  cqo
  idiv rcx
  mov r11, rax
.Lx1_3:
  mov r15, r11
  mov rax, r8
  mov rcx, r9
  test rcx, rcx
  jne .Lx1_5
  xor r11d, r11d
  jmp .Lx1_6
.Lx1_5:
  cmp rcx, -1
  jne .Lx1_7
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx1_7
  xor r11d, r11d
  jmp .Lx1_6
.Lx1_7:
  cqo
  idiv rcx
  mov r11, rdx
.Lx1_6:
  mov [rbp - 56], r11
  mov rax, [rbp - 56]
  mov rcx, r10
  test rcx, rcx
  jne .Lx1_8
  xor r11d, r11d
  jmp .Lx1_9
.Lx1_8:
  cmp rcx, -1
  jne .Lx1_10
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx1_10
  mov r11, rax
  jmp .Lx1_9
.Lx1_10:
  cqo
  idiv rcx
  mov r11, rax
.Lx1_9:
  mov r8, r11
  mov rax, [rbp - 56]
  mov rcx, r10
  test rcx, rcx
  jne .Lx1_11
  xor r11d, r11d
  jmp .Lx1_12
.Lx1_11:
  cmp rcx, -1
  jne .Lx1_13
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx1_13
  xor r11d, r11d
  jmp .Lx1_12
.Lx1_13:
  cqo
  idiv rcx
  mov r11, rdx
.Lx1_12:
  mov r9, r11
  mov r11, r15
  add r11, rbx
  mov [rbp - 64], r11
  mov r11, r8
  add r11, rbx
  mov r15, r11
  mov r11, r9
  add r11, rbx
  mov r8, r11
  mov r11, [rbp - 64]
  shl r11, 56
  shr r11, 56
  mov r9, r11
  mov r11, r15
  shl r11, 56
  shr r11, 56
  mov [rbp - 72], r11
  mov r11, r8
  shl r11, 56
  shr r11, 56
  mov r15, r11
  mov r11, rsi
  mov rax, rdi
  add r11, rax
  mov r8, r11
  mov rax, r8
  mov r11, r9
  mov [rax], r11b
  mov r11, rdi
  add r11, r12
  mov r8, r11
  mov r11, rsi
  mov rax, r8
  add r11, rax
  mov r9, r11
  mov rax, r9
  mov r11, [rbp - 72]
  mov [rax], r11b
  mov r11, rdi
  add r11, r13
  mov r8, r11
  mov r11, rsi
  mov rax, r8
  add r11, rax
  mov r9, r11
  mov rax, r9
  mov r11, r15
  mov [rax], r11b
  mov r11, rdi
  add r11, r14
  mov rsi, r11
  mov rax, rsi
  mov rbx, [rbp - 16]
  mov r12, [rbp - 24]
  mov r13, [rbp - 32]
  mov r14, [rbp - 40]
  mov r15, [rbp - 48]
  leave
  ret
.Lb1_2:
  mov r11, r8
  mov rax, r10
  cmp r11, rax
  setge al
  movzx eax, al
  mov r9, rax
  mov r11, r9
  test r11, r11
  je .Lx1_14
  jmp .Lb1_3
.Lx1_14:
  jmp .Lb1_4
.Lb1_3:
  mov rax, r8
  mov rcx, r10
  test rcx, rcx
  jne .Lx1_15
  xor r11d, r11d
  jmp .Lx1_16
.Lx1_15:
  cmp rcx, -1
  jne .Lx1_17
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx1_17
  mov r11, rax
  jmp .Lx1_16
.Lx1_17:
  cqo
  idiv rcx
  mov r11, rax
.Lx1_16:
  mov r9, r11
  mov rax, r8
  mov rcx, r10
  test rcx, rcx
  jne .Lx1_18
  xor r11d, r11d
  jmp .Lx1_19
.Lx1_18:
  cmp rcx, -1
  jne .Lx1_20
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx1_20
  xor r11d, r11d
  jmp .Lx1_19
.Lx1_20:
  cqo
  idiv rcx
  mov r11, rdx
.Lx1_19:
  mov r14, r11
  mov r11, r9
  add r11, rbx
  mov r8, r11
  mov r11, r14
  add r11, rbx
  mov r9, r11
  mov r11, r8
  shl r11, 56
  shr r11, 56
  mov r10, r11
  mov r11, r9
  shl r11, 56
  shr r11, 56
  mov r8, r11
  mov r11, rsi
  mov rax, rdi
  add r11, rax
  mov r9, r11
  mov rax, r9
  mov r11, r10
  mov [rax], r11b
  mov r11, rdi
  add r11, r12
  mov r9, r11
  mov r11, rsi
  mov rax, r9
  add r11, rax
  mov r10, r11
  mov rax, r10
  mov r11, r8
  mov [rax], r11b
  mov r11, rdi
  add r11, r13
  mov rsi, r11
  mov rax, rsi
  mov rbx, [rbp - 16]
  mov r12, [rbp - 24]
  mov r13, [rbp - 32]
  mov r14, [rbp - 40]
  mov r15, [rbp - 48]
  leave
  ret
.Lb1_4:
  mov r11, r8
  add r11, rbx
  mov r9, r11
  mov r11, r9
  shl r11, 56
  shr r11, 56
  mov r8, r11
  mov r11, rsi
  mov rax, rdi
  add r11, rax
  mov r9, r11
  mov rax, r9
  mov r11, r8
  mov [rax], r11b
  mov r11, rdi
  add r11, r12
  mov rsi, r11
  mov rax, rsi
  mov rbx, [rbp - 16]
  mov r12, [rbp - 24]
  mov r13, [rbp - 32]
  mov r14, [rbp - 40]
  mov r15, [rbp - 48]
  leave
  ret
.size put_u8, .-put_u8
.globl put_digits6
.type put_digits6, @function
put_digits6:
  push rbp
  mov rbp, rsp
  sub rsp, 128
  mov [rbp - 16], rbx
  mov [rbp - 24], r12
  mov [rbp - 32], r13
  mov [rbp - 40], r14
  mov [rbp - 48], r15
  mov r8, rdx
  mov r11, rdi
  mov rdi, rsi
  mov rsi, r11
.Lb2_0:
  mov r11, 1000000
  mov r9, r11
  mov r11, 100000
  mov r10, r11
  mov r11, 10000
  mov rbx, r11
  mov r11, 1000
  mov r12, r11
  mov r11, 100
  mov r13, r11
  mov r11, 10
  mov r14, r11
  mov r11, 48
  mov r15, r11
  mov r11, 1
  mov [rbp - 56], r11
  mov r11, 2
  mov [rbp - 64], r11
  mov r11, 3
  mov [rbp - 72], r11
  mov r11, 4
  mov [rbp - 80], r11
  mov r11, 5
  mov [rbp - 88], r11
  mov r11, 6
  mov [rbp - 96], r11
  mov rax, r8
  mov rcx, r9
  test rcx, rcx
  jne .Lx2_1
  xor r11d, r11d
  jmp .Lx2_2
.Lx2_1:
  cmp rcx, -1
  jne .Lx2_3
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_3
  xor r11d, r11d
  jmp .Lx2_2
.Lx2_3:
  cqo
  idiv rcx
  mov r11, rdx
.Lx2_2:
  mov [rbp - 104], r11
  mov rax, [rbp - 104]
  mov rcx, r10
  test rcx, rcx
  jne .Lx2_4
  xor r11d, r11d
  jmp .Lx2_5
.Lx2_4:
  cmp rcx, -1
  jne .Lx2_6
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_6
  mov r11, rax
  jmp .Lx2_5
.Lx2_6:
  cqo
  idiv rcx
  mov r11, rax
.Lx2_5:
  mov r8, r11
  mov rax, [rbp - 104]
  mov rcx, r10
  test rcx, rcx
  jne .Lx2_7
  xor r11d, r11d
  jmp .Lx2_8
.Lx2_7:
  cmp rcx, -1
  jne .Lx2_9
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_9
  xor r11d, r11d
  jmp .Lx2_8
.Lx2_9:
  cqo
  idiv rcx
  mov r11, rdx
.Lx2_8:
  mov r9, r11
  mov rax, r9
  mov rcx, rbx
  test rcx, rcx
  jne .Lx2_10
  xor r11d, r11d
  jmp .Lx2_11
.Lx2_10:
  cmp rcx, -1
  jne .Lx2_12
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_12
  mov r11, rax
  jmp .Lx2_11
.Lx2_12:
  cqo
  idiv rcx
  mov r11, rax
.Lx2_11:
  mov r10, r11
  mov rax, r9
  mov rcx, rbx
  test rcx, rcx
  jne .Lx2_13
  xor r11d, r11d
  jmp .Lx2_14
.Lx2_13:
  cmp rcx, -1
  jne .Lx2_15
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_15
  xor r11d, r11d
  jmp .Lx2_14
.Lx2_15:
  cqo
  idiv rcx
  mov r11, rdx
.Lx2_14:
  mov [rbp - 112], r11
  mov rax, [rbp - 112]
  mov rcx, r12
  test rcx, rcx
  jne .Lx2_16
  xor r11d, r11d
  jmp .Lx2_17
.Lx2_16:
  cmp rcx, -1
  jne .Lx2_18
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_18
  mov r11, rax
  jmp .Lx2_17
.Lx2_18:
  cqo
  idiv rcx
  mov r11, rax
.Lx2_17:
  mov r9, r11
  mov rax, [rbp - 112]
  mov rcx, r12
  test rcx, rcx
  jne .Lx2_19
  xor r11d, r11d
  jmp .Lx2_20
.Lx2_19:
  cmp rcx, -1
  jne .Lx2_21
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_21
  xor r11d, r11d
  jmp .Lx2_20
.Lx2_21:
  cqo
  idiv rcx
  mov r11, rdx
.Lx2_20:
  mov rbx, r11
  mov rax, rbx
  mov rcx, r13
  test rcx, rcx
  jne .Lx2_22
  xor r11d, r11d
  jmp .Lx2_23
.Lx2_22:
  cmp rcx, -1
  jne .Lx2_24
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_24
  mov r11, rax
  jmp .Lx2_23
.Lx2_24:
  cqo
  idiv rcx
  mov r11, rax
.Lx2_23:
  mov r12, r11
  mov rax, rbx
  mov rcx, r13
  test rcx, rcx
  jne .Lx2_25
  xor r11d, r11d
  jmp .Lx2_26
.Lx2_25:
  cmp rcx, -1
  jne .Lx2_27
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_27
  xor r11d, r11d
  jmp .Lx2_26
.Lx2_27:
  cqo
  idiv rcx
  mov r11, rdx
.Lx2_26:
  mov [rbp - 120], r11
  mov rax, [rbp - 120]
  mov rcx, r14
  test rcx, rcx
  jne .Lx2_28
  xor r11d, r11d
  jmp .Lx2_29
.Lx2_28:
  cmp rcx, -1
  jne .Lx2_30
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_30
  mov r11, rax
  jmp .Lx2_29
.Lx2_30:
  cqo
  idiv rcx
  mov r11, rax
.Lx2_29:
  mov rbx, r11
  mov rax, [rbp - 120]
  mov rcx, r14
  test rcx, rcx
  jne .Lx2_31
  xor r11d, r11d
  jmp .Lx2_32
.Lx2_31:
  cmp rcx, -1
  jne .Lx2_33
  mov rdx, -9223372036854775808
  cmp rax, rdx
  jne .Lx2_33
  xor r11d, r11d
  jmp .Lx2_32
.Lx2_33:
  cqo
  idiv rcx
  mov r11, rdx
.Lx2_32:
  mov r13, r11
  mov r11, r8
  add r11, r15
  mov r14, r11
  mov r11, r10
  add r11, r15
  mov r8, r11
  mov r11, r9
  add r11, r15
  mov r10, r11
  mov r11, r12
  add r11, r15
  mov r9, r11
  mov r11, rbx
  add r11, r15
  mov r12, r11
  mov r11, r13
  add r11, r15
  mov rbx, r11
  mov r11, r14
  shl r11, 56
  shr r11, 56
  mov r13, r11
  mov r11, r8
  shl r11, 56
  shr r11, 56
  mov r14, r11
  mov r11, r10
  shl r11, 56
  shr r11, 56
  mov r8, r11
  mov r11, r9
  shl r11, 56
  shr r11, 56
  mov r10, r11
  mov r11, r12
  shl r11, 56
  shr r11, 56
  mov r9, r11
  mov r11, rbx
  shl r11, 56
  shr r11, 56
  mov r12, r11
  mov r11, rsi
  mov rax, rdi
  add r11, rax
  mov rbx, r11
  mov rax, rbx
  mov r11, r13
  mov [rax], r11b
  mov r11, rdi
  add r11, [rbp - 56]
  mov rbx, r11
  mov r11, rsi
  mov rax, rbx
  add r11, rax
  mov r13, r11
  mov rax, r13
  mov r11, r14
  mov [rax], r11b
  mov r11, rdi
  add r11, [rbp - 64]
  mov rbx, r11
  mov r11, rsi
  mov rax, rbx
  add r11, rax
  mov r13, r11
  mov rax, r13
  mov r11, r8
  mov [rax], r11b
  mov r11, rdi
  add r11, [rbp - 72]
  mov r8, r11
  mov r11, rsi
  mov rax, r8
  add r11, rax
  mov rbx, r11
  mov rax, rbx
  mov r11, r10
  mov [rax], r11b
  mov r11, rdi
  add r11, [rbp - 80]
  mov r8, r11
  mov r11, rsi
  mov rax, r8
  add r11, rax
  mov r10, r11
  mov rax, r10
  mov r11, r9
  mov [rax], r11b
  mov r11, rdi
  add r11, [rbp - 88]
  mov r8, r11
  mov r11, rsi
  mov rax, r8
  add r11, rax
  mov r9, r11
  mov rax, r9
  mov r11, r12
  mov [rax], r11b
  mov r11, rdi
  add r11, [rbp - 96]
  mov rsi, r11
  mov rax, rsi
  mov rbx, [rbp - 16]
  mov r12, [rbp - 24]
  mov r13, [rbp - 32]
  mov r14, [rbp - 40]
  mov r15, [rbp - 48]
  leave
  ret
.size put_digits6, .-put_digits6
.globl put_color
.type put_color, @function
put_color:
  push rbp
  mov rbp, rsp
  sub rsp, 208
  mov [rbp - 16], rbx
  mov [rbp - 24], r12
  mov [rbp - 32], r13
  mov [rbp - 40], r14
  mov [rbp - 48], r15
  mov rbx, rdi
  mov r12, rdx
  mov rdi, rcx
  shl r12, 32
  shr r12, 32
  shl rdi, 32
  shr rdi, 32
.Lb3_0:
  mov r11, 27
  shl r11, 56
  shr r11, 56
  mov r8, r11
  mov r11, 91
  shl r11, 56
  shr r11, 56
  mov r9, r11
  mov r11, 51
  shl r11, 56
  shr r11, 56
  mov r10, r11
  mov r11, 52
  shl r11, 56
  shr r11, 56
  mov r13, r11
  mov r11, 56
  shl r11, 56
  shr r11, 56
  mov r14, r11
  mov r11, 59
  shl r11, 56
  shr r11, 56
  mov r15, r11
  mov r11, 50
  shl r11, 56
  shr r11, 56
  mov [rbp - 56], r11
  mov r11, 109
  shl r11, 56
  shr r11, 56
  mov [rbp - 64], r11
  mov r11, 1
  mov [rbp - 72], r11
  mov r11, 2
  mov [rbp - 80], r11
  mov r11, 3
  mov [rbp - 88], r11
  mov r11, 4
  mov [rbp - 96], r11
  mov r11, 5
  mov [rbp - 104], r11
  mov r11, 6
  mov [rbp - 112], r11
  mov r11, 7
  mov [rbp - 120], r11
  mov r11, 16
  shl r11, 32
  shr r11, 32
  mov [rbp - 128], r11
  mov r11, 8
  shl r11, 32
  shr r11, 32
  mov [rbp - 136], r11
  mov r11, 255
  shl r11, 32
  shr r11, 32
  mov [rbp - 144], r11
  mov r11, 0
  shl r11, 32
  shr r11, 32
  mov [rbp - 152], r11
  mov r11, rbx
  mov rax, rsi
  add r11, rax
  mov [rbp - 160], r11
  mov rax, [rbp - 160]
  mov r11, r8
  mov [rax], r11b
  mov r11, rsi
  add r11, [rbp - 72]
  mov r8, r11
  mov r11, rbx
  mov rax, r8
  add r11, rax
  mov [rbp - 168], r11
  mov rax, [rbp - 168]
  mov r11, r9
  mov [rax], r11b
  mov r11, rsi
  add r11, [rbp - 80]
  mov r8, r11
  mov r11, rbx
  mov rax, r8
  add r11, rax
  mov r9, r11
  mov r11, rdi
  mov rax, [rbp - 152]
  cmp r11, rax
  setne al
  movzx eax, al
  mov r8, rax
  mov r11, r10
  mov rdi, r11
  mov r11, r8
  test r11, r11
  je .Lx3_1
  mov r11, r13
  mov rdi, r11
.Lx3_1:
  mov rax, r9
  mov r11, rdi
  mov [rax], r11b
  mov r11, rsi
  add r11, [rbp - 88]
  mov rdi, r11
  mov r11, rbx
  mov rax, rdi
  add r11, rax
  mov r8, r11
  mov rax, r8
  mov r11, r14
  mov [rax], r11b
  mov r11, rsi
  add r11, [rbp - 96]
  mov rdi, r11
  mov r11, rbx
  mov rax, rdi
  add r11, rax
  mov r8, r11
  mov rax, r8
  mov r11, r15
  mov [rax], r11b
  mov r11, rsi
  add r11, [rbp - 104]
  mov rdi, r11
  mov r11, rbx
  mov rax, rdi
  add r11, rax
  mov r8, r11
  mov rax, r8
  mov r11, [rbp - 56]
  mov [rax], r11b
  mov r11, rsi
  add r11, [rbp - 112]
  mov rdi, r11
  mov r11, rbx
  mov rax, rdi
  add r11, rax
  mov r8, r11
  mov rax, r8
  mov r11, r15
  mov [rax], r11b
  mov r11, rsi
  add r11, [rbp - 120]
  mov rdi, r11
  mov r11, r12
  shr r11d, 16
  shl r11, 32
  shr r11, 32
  mov rsi, r11
  mov r11, rsi
  and r11d, [rbp - 144]
  shl r11, 32
  shr r11, 32
  mov r8, r11
  mov r11, r8
  mov rsi, r11
  mov rdx, rsi
  mov rsi, rdi
  mov rdi, rbx
  call put_u8
  mov r8, rax
  mov r11, rbx
  mov rax, r8
  add r11, rax
  mov rsi, r11
  mov rax, rsi
  mov r11, r15
  mov [rax], r11b
  mov r11, r8
  add r11, [rbp - 72]
  mov rsi, r11
  mov r11, r12
  shr r11d, 8
  shl r11, 32
  shr r11, 32
  mov rdi, r11
  mov r11, rdi
  and r11d, [rbp - 144]
  shl r11, 32
  shr r11, 32
  mov r8, r11
  mov r11, r8
  mov rdi, r11
  mov rdx, rdi
  mov rdi, rbx
  call put_u8
  mov r8, rax
  mov r11, rbx
  mov rax, r8
  add r11, rax
  mov rsi, r11
  mov rax, rsi
  mov r11, r15
  mov [rax], r11b
  mov r11, r8
  add r11, [rbp - 72]
  mov rsi, r11
  mov r11, r12
  and r11d, [rbp - 144]
  shl r11, 32
  shr r11, 32
  mov rdi, r11
  mov r11, rdi
  mov r8, r11
  mov rdi, rbx
  mov rdx, r8
  call put_u8
  mov rdi, rax
  mov r11, rbx
  mov rax, rdi
  add r11, rax
  mov rsi, r11
  mov rax, rsi
  mov r11, [rbp - 64]
  mov [rax], r11b
  mov r11, rdi
  add r11, [rbp - 72]
  mov rsi, r11
  mov rax, rsi
  mov rbx, [rbp - 16]
  mov r12, [rbp - 24]
  mov r13, [rbp - 32]
  mov r14, [rbp - 40]
  mov r15, [rbp - 48]
  leave
  ret
.size put_color, .-put_color
.globl make_line
.type make_line, @function
make_line:
  push rbp
  mov rbp, rsp
  sub rsp, 96
  mov [rbp - 16], rbx
  mov [rbp - 24], r12
  mov [rbp - 32], r13
  mov [rbp - 40], r14
  mov [rbp - 48], r15
  mov r10, r8
  mov rbx, r9
  mov r8, rdx
  mov r9, rcx
  mov r11, rdi
  mov rdi, rsi
  mov rsi, r11
  shl r8, 56
  shr r8, 56
  shl r9, 56
  shr r9, 56
  shl r10, 56
  shr r10, 56
.Lb4_0:
  mov r11, 0
  mov r12, r11
  mov r11, 1
  mov r13, r11
  mov r11, 2
  mov r14, r11
  mov r11, 10
  shl r11, 56
  shr r11, 56
  mov r15, r11
  mov r11, rsi
  mov rax, rdi
  add r11, rax
  mov [rbp - 56], r11
  mov rax, [rbp - 56]
  mov r11, r8
  mov [rax], r11b
  mov r11, rdi
  add r11, r13
  mov r8, r11
  mov r11, rbx
  sub r11, r14
  mov [rbp - 64], r11
  mov r14, rbx
  mov rbx, r10
  mov r10, [rbp - 64]
  mov r11, r12
  mov r12, rdi
  mov rdi, rsi
  mov rsi, r11
  jmp .Lb4_1
.Lb4_1:
  mov r11, rsi
  mov rax, r10
  cmp r11, rax
  setge al
  movzx eax, al
  mov [rbp - 72], rax
  mov r11, [rbp - 72]
  test r11, r11
  je .Lx4_1
  mov rsi, rdi
  mov rdi, r8
  mov r8, rbx
  mov r9, r12
  mov r10, r14
  jmp .Lb4_3
.Lx4_1:
  jmp .Lb4_2
.Lb4_2:
  mov r11, rdi
  mov rax, r8
  add r11, rax
  mov [rbp - 80], r11
  mov rax, [rbp - 80]
  mov r11, r9
  mov [rax], r11b
  mov r11, r8
  add r11, r13
  mov [rbp - 88], r11
  mov r11, rsi
  add r11, r13
  mov r8, r11
  mov rsi, r8
  mov r8, [rbp - 88]
  jmp .Lb4_1
.Lb4_3:
  mov r11, rsi
  mov rax, rdi
  add r11, rax
  mov r9, r11
  mov rax, r9
  mov r11, r8
  mov [rax], r11b
  mov r11, rdi
  add r11, r13
  mov r8, r11
  mov r11, rsi
  mov rax, r8
  add r11, rax
  mov rdi, r11
  mov rax, rdi
  mov r11, r15
  mov [rax], r11b
  mov r11, r8
  add r11, r13
  mov rsi, r11
  mov rax, rsi
  mov rbx, [rbp - 16]
  mov r12, [rbp - 24]
  mov r13, [rbp - 32]
  mov r14, [rbp - 40]
  mov r15, [rbp - 48]
  leave
  ret
.size make_line, .-make_line
.globl render_plasma
.type render_plasma, @function
render_plasma:
  push rbp
  mov rbp, rsp
  sub rsp, 560
  mov [rbp - 16], rbx
  mov [rbp - 24], r12
  mov [rbp - 32], r13
  mov [rbp - 40], r14
  mov [rbp - 48], r15
  mov r10, r8
  mov rbx, r9
  mov r8, rdx
  mov r9, rcx
  mov r11, rdi
  mov rdi, rsi
  mov rsi, r11
.Lb5_0:
  mov r11, 0
  mov r12, r11
  mov r11, 1
  mov r13, r11
  mov r11, 16
  shl r11, 32
  shr r11, 32
  mov r14, r11
  mov r11, 8
  shl r11, 32
  shr r11, 32
  mov r15, r11
  mov r11, 46
  shl r11, 56
  shr r11, 56
  mov [rbp - 56], r11
  mov r11, 32
  shl r11, 56
  shr r11, 56
  mov [rbp - 64], r11
  mov r11, 0
  shl r11, 32
  shr r11, 32
  mov [rbp - 72], r11
  mov r11, 80
  shl r11, 32
  shr r11, 32
  mov [rbp - 80], r11
  mov r11, 110
  shl r11, 32
  shr r11, 32
  mov [rbp - 88], r11
  mov r11, 160
  shl r11, 32
  shr r11, 32
  mov [rbp - 96], r11
  mov rax, 0x0
  movq xmm15, rax
  movsd [rbp - 320], xmm15
  mov rax, 0x3fe0000000000000
  movq xmm15, rax
  movsd xmm1, xmm15
  mov rax, 0x4004cccccccccccd
  movq xmm15, rax
  movsd [rbp - 328], xmm15
  mov rax, 0x400999999999999a
  movq xmm15, rax
  movsd [rbp - 336], xmm15
  mov rax, 0x3feccccccccccccd
  movq xmm15, rax
  movsd [rbp - 344], xmm15
  mov rax, 0x3ffccccccccccccd
  movq xmm15, rax
  movsd [rbp - 352], xmm15
  mov rax, 0x3fe6666666666666
  movq xmm15, rax
  movsd [rbp - 360], xmm15
  mov rax, 0x4010000000000000
  movq xmm15, rax
  movsd [rbp - 368], xmm15
  mov rax, 0x3ff6666666666666
  movq xmm15, rax
  movsd [rbp - 376], xmm15
  mov rax, 0x3fd0000000000000
  movq xmm15, rax
  movsd [rbp - 384], xmm15
  mov rax, 0x400921fb53c8d4f1
  movq xmm15, rax
  movsd [rbp - 392], xmm15
  mov rax, 0x3ff921fb4d12d84a
  movq xmm15, rax
  movsd [rbp - 400], xmm15
  mov rax, 0x4030000000000000
  movq xmm15, rax
  movsd [rbp - 408], xmm15
  mov rax, 0x4034000000000000
  movq xmm15, rax
  movsd [rbp - 416], xmm15
  mov rax, 0x4028000000000000
  movq xmm15, rax
  movsd [rbp - 424], xmm15
  mov rax, 0x403e000000000000
  movq xmm15, rax
  movsd [rbp - 432], xmm15
  mov rax, 0x4045000000000000
  movq xmm15, rax
  movsd [rbp - 440], xmm15
  mov rax, 0x3fdae147ae147ae1
  movq xmm15, rax
  movsd [rbp - 448], xmm15
  mov rax, 0x3fe999999999999a
  movq xmm15, rax
  movsd [rbp - 456], xmm15
  mov r11, r10
  cvtsi2sd xmm15, r11
  movsd xmm2, xmm15
  mov r11, rbx
  cvtsi2sd xmm15, r11
  movsd xmm3, xmm15
  movsd xmm15, xmm2
  mulsd xmm15, xmm1
  movsd xmm4, xmm15
  movsd xmm15, xmm3
  mulsd xmm15, xmm1
  movsd xmm2, xmm15
  mov [rbp - 104], rbx
  mov rbx, r10
  mov r10, r9
  mov r9, r8
  mov r8, rdi
  mov rdi, rsi
  mov rsi, r12
  movsd xmm1, xmm4
  jmp .Lb5_1
.Lb5_1:
  mov r11, rsi
  mov rax, [rbp - 104]
  cmp r11, rax
  setge al
  movzx eax, al
  mov [rbp - 112], rax
  mov r11, [rbp - 112]
  test r11, r11
  je .Lx5_1
  jmp .Lb5_7
.Lx5_1:
  mov [rbp - 120], rbx
  mov r11, [rbp - 104]
  mov [rbp - 128], r11
  mov rbx, r10
  mov r10, r9
  mov r9, r8
  mov r8, rdi
  mov rdi, rsi
  mov rsi, r12
  jmp .Lb5_2
.Lb5_2:
  mov r11, rsi
  mov rax, [rbp - 120]
  cmp r11, rax
  setge al
  movzx eax, al
  mov [rbp - 136], rax
  mov r11, [rbp - 136]
  test r11, r11
  je .Lx5_2
  mov rsi, rdi
  mov rdi, r8
  mov r8, r9
  mov r9, r10
  mov r10, rbx
  mov rbx, [rbp - 120]
  mov r11, [rbp - 128]
  mov [rbp - 144], r11
  jmp .Lb5_3
.Lx5_2:
  mov [rbp - 160], rdi
  mov [rbp - 168], r8
  mov [rbp - 176], r9
  mov [rbp - 184], r10
  mov [rbp - 192], rbx
  mov r11, [rbp - 120]
  mov [rbp - 200], r11
  mov r11, [rbp - 128]
  mov [rbp - 208], r11
  mov rbx, rsi
  movsd [rbp - 464], xmm0
  movsd [rbp - 472], xmm1
  movsd [rbp - 480], xmm2
  jmp .Lb5_4
.Lb5_3:
  mov r11, rsi
  add r11, r13
  mov [rbp - 152], r11
  mov rsi, [rbp - 152]
  mov r11, [rbp - 144]
  mov [rbp - 104], r11
  jmp .Lb5_1
.Lb5_4:
  mov r11, [rbp - 160]
  imul r11, [rbp - 200]
  mov rsi, r11
  mov r11, rsi
  add r11, rbx
  mov [rbp - 216], r11
  mov r11, [rbp - 192]
  mov rax, [rbp - 216]
  imul rax, rax, 8
  add r11, rax
  mov rsi, r11
  mov rax, rsi
  movsd xmm15, [rbp - 320]
  movsd [rax], xmm15
  mov r11, rbx
  cvtsi2sd xmm15, r11
  movsd xmm0, xmm15
  mov r11, [rbp - 160]
  cvtsi2sd xmm15, r11
  movsd xmm1, xmm15
  movsd xmm15, xmm0
  subsd xmm15, [rbp - 472]
  movsd xmm2, xmm15
  movsd xmm15, xmm1
  subsd xmm15, [rbp - 480]
  movsd xmm0, xmm15
  movsd xmm15, xmm2
  divsd xmm15, [rbp - 472]
  movsd [rbp - 488], xmm15
  movsd xmm15, xmm0
  divsd xmm15, [rbp - 480]
  movsd [rbp - 496], xmm15
  movsd xmm15, [rbp - 488]
  mulsd xmm15, [rbp - 328]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  addsd xmm15, [rbp - 464]
  movsd xmm1, xmm15
  movsd xmm0, xmm1
  call sin
  movsd [rbp - 504], xmm0
  movsd xmm15, [rbp - 496]
  mulsd xmm15, [rbp - 336]
  movsd xmm0, xmm15
  movsd xmm15, [rbp - 464]
  mulsd xmm15, [rbp - 344]
  movsd xmm1, xmm15
  movsd xmm15, xmm0
  subsd xmm15, xmm1
  movsd xmm2, xmm15
  movsd xmm0, xmm2
  call cos
  movsd [rbp - 512], xmm0
  movsd xmm15, [rbp - 488]
  addsd xmm15, [rbp - 496]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  mulsd xmm15, [rbp - 352]
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 464]
  mulsd xmm15, [rbp - 360]
  movsd xmm0, xmm15
  movsd xmm15, xmm1
  addsd xmm15, xmm0
  movsd xmm2, xmm15
  movsd xmm0, xmm2
  call sin
  movsd [rbp - 520], xmm0
  movsd xmm15, [rbp - 488]
  mulsd xmm15, [rbp - 488]
  movsd xmm0, xmm15
  movsd xmm15, [rbp - 496]
  mulsd xmm15, [rbp - 496]
  movsd xmm1, xmm15
  movsd xmm15, xmm0
  addsd xmm15, xmm1
  movsd xmm2, xmm15
  movsd xmm0, xmm2
  call sqrt
  movsd xmm15, xmm0
  mulsd xmm15, [rbp - 368]
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 464]
  mulsd xmm15, [rbp - 376]
  movsd xmm0, xmm15
  movsd xmm15, xmm1
  subsd xmm15, xmm0
  movsd xmm2, xmm15
  movsd xmm0, xmm2
  call cos
  movsd xmm15, [rbp - 504]
  addsd xmm15, [rbp - 512]
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 520]
  addsd xmm15, xmm0
  movsd xmm2, xmm15
  movsd xmm15, xmm1
  addsd xmm15, xmm2
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  mulsd xmm15, [rbp - 384]
  movsd [rbp - 528], xmm15
  movsd xmm15, [rbp - 528]
  mulsd xmm15, [rbp - 392]
  movsd [rbp - 536], xmm15
  movsd xmm15, [rbp - 536]
  addsd xmm15, [rbp - 464]
  movsd xmm0, xmm15
  call sin
  movsd xmm1, xmm0
  movsd xmm15, xmm1
  mulsd xmm15, [rbp - 408]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  addsd xmm15, [rbp - 416]
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx5_4
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx5_3
  jb .Lx5_4
  mov r11, 0x7fffffffffffffff
  jmp .Lx5_4
.Lx5_3:
  xor r11d, r11d
.Lx5_4:
  mov rax, 2147483647
  cmp r11, rax
  cmovg r11, rax
  mov rax, -2147483648
  cmp r11, rax
  cmovl r11, rax
  shl r11, 32
  shr r11, 32
  mov [rbp - 224], r11
  movsd xmm15, [rbp - 464]
  mulsd xmm15, [rbp - 456]
  movsd xmm0, xmm15
  movsd xmm15, [rbp - 536]
  subsd xmm15, xmm0
  movsd xmm1, xmm15
  movsd xmm0, xmm1
  call cos
  movsd xmm15, xmm0
  mulsd xmm15, [rbp - 424]
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  addsd xmm15, [rbp - 408]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx5_6
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx5_5
  jb .Lx5_6
  mov r11, 0x7fffffffffffffff
  jmp .Lx5_6
.Lx5_5:
  xor r11d, r11d
.Lx5_6:
  mov rax, 2147483647
  cmp r11, rax
  cmovg r11, rax
  mov rax, -2147483648
  cmp r11, rax
  cmovl r11, rax
  shl r11, 32
  shr r11, 32
  mov [rbp - 232], r11
  movsd xmm15, [rbp - 528]
  mulsd xmm15, [rbp - 400]
  movsd xmm0, xmm15
  mov rax, 0x3ff3333333333333
  movq xmm15, rax
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 464]
  mulsd xmm15, xmm1
  movsd xmm2, xmm15
  movsd xmm15, xmm0
  addsd xmm15, xmm2
  movsd xmm1, xmm15
  movsd xmm0, xmm1
  call sin
  movsd xmm15, xmm0
  mulsd xmm15, [rbp - 432]
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  addsd xmm15, [rbp - 440]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx5_8
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx5_7
  jb .Lx5_8
  mov r11, 0x7fffffffffffffff
  jmp .Lx5_8
.Lx5_7:
  xor r11d, r11d
.Lx5_8:
  mov rax, 2147483647
  cmp r11, rax
  cmovg r11, rax
  mov rax, -2147483648
  cmp r11, rax
  cmovl r11, rax
  shl r11, 32
  shr r11, 32
  mov rsi, r11
  mov r11, [rbp - 224]
  shl r11d, 16
  shl r11, 32
  shr r11, 32
  mov rdi, r11
  mov r11, [rbp - 232]
  shl r11d, 8
  shl r11, 32
  shr r11, 32
  mov r8, r11
  mov r11, rdi
  or r11d, r8d
  shl r11, 32
  shr r11, 32
  mov r9, r11
  mov r11, r9
  or r11d, esi
  shl r11, 32
  shr r11, 32
  mov rdi, r11
  mov r11, [rbp - 184]
  mov rax, [rbp - 216]
  imul rax, rax, 4
  add r11, rax
  mov r8, r11
  mov rax, r8
  mov r11, rdi
  mov [rax], r11d
  movsd xmm15, [rbp - 528]
  xor eax, eax
  ucomisd xmm15, [rbp - 448]
  setp r11b
  seta al
  xor r11b, 1
  and al, r11b
  movzx eax, al
  mov rdi, rax
  mov r11, rdi
  test r11, r11
  je .Lx5_9
  mov rdi, [rbp - 176]
  mov r8, [rbp - 216]
  mov r9, [rbp - 224]
  mov r10, [rbp - 232]
  mov [rbp - 240], rbx
  mov r11, [rbp - 160]
  mov [rbp - 248], r11
  mov r11, [rbp - 200]
  mov [rbp - 256], r11
  mov r11, [rbp - 208]
  mov [rbp - 264], r11
  mov rbx, rsi
  mov rsi, [rbp - 168]
  movsd xmm0, [rbp - 464]
  movsd xmm1, [rbp - 472]
  movsd xmm2, [rbp - 480]
  jmp .Lb5_5
.Lx5_9:
  mov rsi, [rbp - 168]
  mov rdi, [rbp - 176]
  mov r8, [rbp - 216]
  mov r9, rbx
  mov r10, [rbp - 160]
  mov rbx, [rbp - 200]
  mov r11, [rbp - 208]
  mov [rbp - 296], r11
  movsd xmm0, [rbp - 464]
  movsd xmm1, [rbp - 472]
  movsd xmm2, [rbp - 480]
  jmp .Lb5_6
.Lb5_5:
  mov r11, rsi
  mov rax, r8
  add r11, rax
  mov [rbp - 272], r11
  mov rax, [rbp - 272]
  mov r11, [rbp - 56]
  mov [rax], r11b
  mov r11, r9
  add r11d, [rbp - 80]
  shl r11, 32
  shr r11, 32
  mov [rbp - 280], r11
  mov r11, r10
  add r11d, [rbp - 88]
  shl r11, 32
  shr r11, 32
  mov r9, r11
  mov r11, rbx
  add r11d, [rbp - 96]
  shl r11, 32
  shr r11, 32
  mov r10, r11
  mov r11, [rbp - 280]
  shl r11d, 16
  shl r11, 32
  shr r11, 32
  mov rbx, r11
  mov r11, r9
  shl r11d, 8
  shl r11, 32
  shr r11, 32
  mov [rbp - 288], r11
  mov r11, rbx
  or r11d, [rbp - 288]
  shl r11, 32
  shr r11, 32
  mov r9, r11
  mov r11, r9
  or r11d, r10d
  shl r11, 32
  shr r11, 32
  mov rbx, r11
  mov r11, rdi
  mov rax, r8
  imul rax, rax, 4
  add r11, rax
  mov r9, r11
  mov rax, r9
  mov r11, rbx
  mov [rax], r11d
  mov r11, [rbp - 240]
  add r11, r13
  mov r8, r11
  mov r9, rdi
  mov r10, [rbp - 184]
  mov rbx, [rbp - 192]
  mov r11, [rbp - 256]
  mov [rbp - 120], r11
  mov r11, [rbp - 264]
  mov [rbp - 128], r11
  mov rdi, [rbp - 248]
  mov r11, r8
  mov r8, rsi
  mov rsi, r11
  jmp .Lb5_2
.Lb5_6:
  mov r11, rsi
  mov rax, r8
  add r11, rax
  mov [rbp - 304], r11
  mov rax, [rbp - 304]
  mov r11, [rbp - 64]
  mov [rax], r11b
  mov r11, rdi
  mov rax, r8
  imul rax, rax, 4
  add r11, rax
  mov [rbp - 312], r11
  mov rax, [rbp - 312]
  mov r11, [rbp - 72]
  mov [rax], r11d
  mov r11, r9
  add r11, r13
  mov r8, r11
  mov r9, rdi
  mov [rbp - 120], rbx
  mov r11, [rbp - 296]
  mov [rbp - 128], r11
  mov rdi, r10
  mov r10, [rbp - 184]
  mov rbx, [rbp - 192]
  mov r11, r8
  mov r8, rsi
  mov rsi, r11
  jmp .Lb5_2
.Lb5_7:
  mov rbx, [rbp - 16]
  mov r12, [rbp - 24]
  mov r13, [rbp - 32]
  mov r14, [rbp - 40]
  mov r15, [rbp - 48]
  leave
  ret
.size render_plasma, .-render_plasma
.globl render_ring
.type render_ring, @function
render_ring:
  push rbp
  mov rbp, rsp
  sub rsp, 1360
  mov [rbp - 16], rbx
  mov [rbp - 24], r12
  mov [rbp - 32], r13
  mov [rbp - 40], r14
  mov [rbp - 48], r15
  mov rbx, rdi
  mov r12, rsi
  mov r13, rdx
  mov r14, rcx
  mov r15, r8
  mov [rbp - 56], r9
  mov r11, [rbp + 16]
  mov [rbp - 64], r11
  mov r11, [rbp + 24]
  mov [rbp - 72], r11
  movsd [rbp - 288], xmm0
  movsd [rbp - 296], xmm1
  movsd [rbp - 304], xmm2
  movsd [rbp - 312], xmm3
  movsd [rbp - 320], xmm4
  movsd [rbp - 328], xmm5
.Lb6_0:
  mov r11, 0
  mov [rbp - 80], r11
  mov r11, 1
  mov rsi, r11
  mov r11, 8
  shl r11, 32
  shr r11, 32
  mov [rbp - 88], r11
  mov r11, 16
  shl r11, 32
  shr r11, 32
  mov [rbp - 96], r11
  mov r11, 12
  mov [rbp - 104], r11
  mov rax, 0x0
  movq xmm15, rax
  movsd [rbp - 336], xmm15
  mov rax, 0x3ff0000000000000
  movq xmm15, rax
  movsd [rbp - 344], xmm15
  mov rax, 0x3fe0000000000000
  movq xmm15, rax
  movsd [rbp - 352], xmm15
  mov rax, 0x3ff4000000000000
  movq xmm15, rax
  movsd [rbp - 360], xmm15
  mov rax, 0x4000666666666666
  movq xmm15, rax
  movsd [rbp - 368], xmm15
  mov rax, 0x401921fb53c8d4f1
  movq xmm15, rax
  movsd [rbp - 376], xmm15
  mov rax, 0x3fb70a3d70a3d70a
  movq xmm15, rax
  movsd [rbp - 384], xmm15
  mov rax, 0x3fa1eb851eb851ec
  movq xmm15, rax
  movsd [rbp - 392], xmm15
  mov rax, 0x4028000000000000
  movq xmm15, rax
  movsd [rbp - 400], xmm15
  mov rax, 0x3fe8000000000000
  movq xmm15, rax
  movsd [rbp - 408], xmm15
  mov rax, 0x3fd0000000000000
  movq xmm15, rax
  movsd [rbp - 416], xmm15
  mov rax, 0x406fe00000000000
  movq xmm15, rax
  movsd [rbp - 424], xmm15
  mov rax, 0x3ff4cccccccccccd
  movq xmm15, rax
  movsd [rbp - 432], xmm15
  mov rax, 0x3fe6666666666666
  movq xmm15, rax
  movsd [rbp - 440], xmm15
  mov rax, 0x4000000000000000
  movq xmm15, rax
  movsd [rbp - 448], xmm15
  mov rax, 0x3ff8000000000000
  movq xmm15, rax
  movsd [rbp - 456], xmm15
  mov rax, 0x3fdccccccccccccd
  movq xmm15, rax
  movsd [rbp - 464], xmm15
  mov rax, 0x3fe199999999999a
  movq xmm15, rax
  movsd [rbp - 472], xmm15
  mov rax, 0x3fe999999999999a
  movq xmm15, rax
  movsd [rbp - 480], xmm15
  mov rax, 0x3fc999999999999a
  movq xmm15, rax
  movsd [rbp - 488], xmm15
  movsd xmm0, [rbp - 288]
  call cos
  movsd [rbp - 496], xmm0
  movsd xmm0, [rbp - 288]
  call sin
  movsd [rbp - 504], xmm0
  movsd xmm0, [rbp - 296]
  call cos
  movsd [rbp - 512], xmm0
  movsd xmm0, [rbp - 296]
  call sin
  mov r11, [rbp - 56]
  cvtsi2sd xmm15, r11
  movsd xmm1, xmm15
  mov r11, [rbp - 64]
  cvtsi2sd xmm15, r11
  movsd xmm2, xmm15
  movsd xmm15, xmm1
  mulsd xmm15, [rbp - 352]
  movsd xmm3, xmm15
  movsd xmm15, xmm2
  mulsd xmm15, [rbp - 352]
  movsd xmm1, xmm15
  movsd xmm15, xmm2
  mulsd xmm15, [rbp - 360]
  movsd xmm4, xmm15
  mov rsi, rbx
  mov rdi, r12
  mov r8, r13
  mov r9, r14
  mov r10, r15
  mov rbx, [rbp - 56]
  mov r12, [rbp - 64]
  mov r13, [rbp - 72]
  movsd xmm2, [rbp - 504]
  movsd xmm5, [rbp - 304]
  movsd xmm6, [rbp - 312]
  movsd xmm7, [rbp - 320]
  movsd xmm8, [rbp - 328]
  movsd xmm9, xmm3
  movsd xmm10, xmm1
  movsd xmm11, xmm4
  movsd xmm12, [rbp - 368]
  movsd xmm1, [rbp - 496]
  movsd xmm3, [rbp - 512]
  movsd xmm4, xmm0
  movsd xmm0, [rbp - 336]
  jmp .Lb6_1
.Lb6_1:
  movsd xmm15, xmm0
  xor eax, eax
  ucomisd xmm15, [rbp - 376]
  setp r11b
  seta al
  xor r11b, 1
  and al, r11b
  movzx eax, al
  mov r14, rax
  mov r11, r14
  test r11, r11
  je .Lx6_1
  jmp .Lb6_11
.Lx6_1:
  mov r14, r9
  mov r15, r10
  mov [rbp - 112], rbx
  mov [rbp - 120], r12
  mov [rbp - 128], r13
  mov rbx, rsi
  mov r12, rdi
  mov r13, r8
  movsd [rbp - 520], xmm0
  movsd [rbp - 528], xmm1
  movsd [rbp - 536], xmm2
  movsd [rbp - 544], xmm3
  movsd [rbp - 552], xmm4
  movsd [rbp - 560], xmm5
  movsd [rbp - 568], xmm6
  movsd [rbp - 576], xmm7
  movsd [rbp - 584], xmm8
  movsd [rbp - 592], xmm9
  movsd [rbp - 600], xmm10
  movsd [rbp - 608], xmm11
  movsd [rbp - 616], xmm12
  jmp .Lb6_2
.Lb6_2:
  movsd xmm0, [rbp - 520]
  call cos
  movsd [rbp - 624], xmm0
  movsd xmm0, [rbp - 520]
  call sin
  movsd xmm15, [rbp - 568]
  mulsd xmm15, [rbp - 624]
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 560]
  addsd xmm15, xmm1
  movsd xmm2, xmm15
  mov rsi, rbx
  mov rdi, r12
  mov r8, r13
  mov r9, r14
  mov r10, r15
  mov rbx, [rbp - 112]
  mov r12, [rbp - 120]
  mov r13, [rbp - 128]
  movsd xmm1, [rbp - 520]
  movsd xmm3, [rbp - 536]
  movsd xmm4, [rbp - 544]
  movsd xmm5, [rbp - 552]
  movsd xmm6, [rbp - 560]
  movsd xmm7, [rbp - 568]
  movsd xmm8, [rbp - 576]
  movsd xmm9, [rbp - 584]
  movsd xmm10, [rbp - 592]
  movsd xmm11, [rbp - 600]
  movsd xmm12, [rbp - 608]
  movsd xmm13, [rbp - 616]
  movsd xmm14, [rbp - 624]
  movsd [rbp - 632], xmm0
  movsd [rbp - 640], xmm2
  movsd xmm0, [rbp - 336]
  movsd xmm2, [rbp - 528]
  jmp .Lb6_3
.Lb6_3:
  movsd xmm15, xmm0
  xor eax, eax
  ucomisd xmm15, [rbp - 376]
  setp r11b
  seta al
  xor r11b, 1
  and al, r11b
  movzx eax, al
  mov r14, rax
  mov r11, r14
  test r11, r11
  je .Lx6_2
  movsd xmm0, xmm1
  movsd xmm1, xmm2
  movsd xmm2, xmm3
  movsd xmm3, xmm4
  movsd xmm4, xmm5
  movsd xmm5, xmm6
  movsd xmm6, xmm7
  movsd xmm7, xmm8
  movsd xmm8, xmm9
  movsd xmm9, xmm10
  movsd xmm10, xmm11
  movsd xmm11, xmm12
  movsd xmm12, xmm13
  jmp .Lb6_4
.Lx6_2:
  mov r14, r9
  mov r15, r10
  mov [rbp - 136], rbx
  mov [rbp - 144], r12
  mov [rbp - 152], r13
  mov rbx, rsi
  mov r12, rdi
  mov r13, r8
  movsd [rbp - 648], xmm0
  movsd [rbp - 656], xmm1
  movsd [rbp - 664], xmm2
  movsd [rbp - 672], xmm3
  movsd [rbp - 680], xmm4
  movsd [rbp - 688], xmm5
  movsd [rbp - 696], xmm6
  movsd [rbp - 704], xmm7
  movsd [rbp - 712], xmm8
  movsd [rbp - 720], xmm9
  movsd [rbp - 728], xmm10
  movsd [rbp - 736], xmm11
  movsd [rbp - 744], xmm12
  movsd [rbp - 752], xmm13
  movsd [rbp - 760], xmm14
  movsd xmm15, [rbp - 632]
  movsd [rbp - 768], xmm15
  movsd xmm15, [rbp - 640]
  movsd [rbp - 776], xmm15
  jmp .Lb6_5
.Lb6_4:
  movsd xmm15, xmm0
  addsd xmm15, [rbp - 384]
  movsd xmm13, xmm15
  movsd xmm0, xmm13
  jmp .Lb6_1
.Lb6_5:
  movsd xmm0, [rbp - 648]
  call cos
  movsd [rbp - 784], xmm0
  movsd xmm0, [rbp - 648]
  call sin
  movsd xmm15, [rbp - 680]
  mulsd xmm15, [rbp - 784]
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 672]
  mulsd xmm15, [rbp - 688]
  movsd xmm2, xmm15
  movsd xmm15, xmm2
  mulsd xmm15, xmm0
  movsd xmm3, xmm15
  movsd xmm15, xmm1
  addsd xmm15, xmm3
  movsd xmm2, xmm15
  movsd xmm15, [rbp - 776]
  mulsd xmm15, xmm2
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 664]
  mulsd xmm15, [rbp - 688]
  movsd xmm2, xmm15
  movsd xmm15, [rbp - 704]
  mulsd xmm15, xmm2
  movsd xmm3, xmm15
  movsd xmm15, xmm3
  mulsd xmm15, [rbp - 768]
  movsd xmm2, xmm15
  movsd xmm15, xmm1
  subsd xmm15, xmm2
  movsd xmm3, xmm15
  movsd xmm15, [rbp - 688]
  mulsd xmm15, [rbp - 784]
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 672]
  mulsd xmm15, [rbp - 680]
  movsd xmm2, xmm15
  movsd xmm15, xmm2
  mulsd xmm15, xmm0
  movsd xmm4, xmm15
  movsd xmm15, xmm1
  subsd xmm15, xmm4
  movsd xmm2, xmm15
  movsd xmm15, [rbp - 776]
  mulsd xmm15, xmm2
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 664]
  mulsd xmm15, [rbp - 680]
  movsd xmm2, xmm15
  movsd xmm15, [rbp - 704]
  mulsd xmm15, xmm2
  movsd xmm4, xmm15
  movsd xmm15, xmm4
  mulsd xmm15, [rbp - 768]
  movsd xmm2, xmm15
  movsd xmm15, xmm1
  addsd xmm15, xmm2
  movsd xmm4, xmm15
  movsd xmm15, [rbp - 664]
  mulsd xmm15, [rbp - 776]
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  mulsd xmm15, xmm0
  movsd xmm2, xmm15
  movsd xmm15, [rbp - 704]
  mulsd xmm15, [rbp - 672]
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  mulsd xmm15, [rbp - 768]
  movsd xmm5, xmm15
  movsd xmm15, xmm2
  addsd xmm15, xmm5
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 712]
  addsd xmm15, xmm1
  movsd xmm2, xmm15
  movsd xmm15, [rbp - 344]
  divsd xmm15, xmm2
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 752]
  mulsd xmm15, [rbp - 744]
  movsd xmm2, xmm15
  movsd xmm15, xmm2
  mulsd xmm15, xmm3
  movsd xmm5, xmm15
  movsd xmm15, xmm5
  mulsd xmm15, xmm1
  movsd xmm2, xmm15
  movsd xmm15, [rbp - 728]
  addsd xmm15, xmm2
  movsd xmm3, xmm15
  movsd xmm15, xmm3
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx6_4
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx6_3
  jb .Lx6_4
  mov r11, 0x7fffffffffffffff
  jmp .Lx6_4
.Lx6_3:
  xor r11d, r11d
.Lx6_4:
  mov rsi, r11
  movsd xmm15, [rbp - 744]
  mulsd xmm15, xmm4
  movsd xmm2, xmm15
  movsd xmm15, xmm2
  mulsd xmm15, xmm1
  movsd xmm3, xmm15
  movsd xmm15, [rbp - 736]
  addsd xmm15, xmm3
  movsd xmm2, xmm15
  movsd xmm15, xmm2
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx6_6
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx6_5
  jb .Lx6_6
  mov r11, 0x7fffffffffffffff
  jmp .Lx6_6
.Lx6_5:
  xor r11d, r11d
.Lx6_6:
  mov rdi, r11
  mov r11, rsi
  mov rax, [rbp - 80]
  cmp r11, rax
  setge al
  movzx eax, al
  mov r8, rax
  mov r11, rsi
  mov rax, [rbp - 136]
  cmp r11, rax
  setl al
  movzx eax, al
  mov r9, rax
  mov r11, r8
  and r11d, r9d
  shl r11, 63
  shr r11, 63
  mov r10, r11
  mov r11, rdi
  mov rax, [rbp - 80]
  cmp r11, rax
  setge al
  movzx eax, al
  mov r8, rax
  mov r11, rdi
  mov rax, [rbp - 144]
  cmp r11, rax
  setl al
  movzx eax, al
  mov r9, rax
  mov r11, r8
  and r11d, r9d
  shl r11, 63
  shr r11, 63
  mov [rbp - 160], r11
  mov r11, r10
  and r11d, [rbp - 160]
  shl r11, 63
  shr r11, 63
  mov r8, r11
  mov r11, r8
  test r11, r11
  je .Lx6_7
  mov r8, r13
  mov r9, r14
  mov r10, r15
  mov r13, [rbp - 152]
  mov r14, rsi
  mov r15, rdi
  mov rsi, rbx
  mov rdi, r12
  mov rbx, [rbp - 136]
  mov r12, [rbp - 144]
  movsd xmm2, [rbp - 664]
  movsd xmm3, [rbp - 672]
  movsd xmm4, [rbp - 680]
  movsd xmm5, [rbp - 688]
  movsd xmm6, [rbp - 696]
  movsd xmm7, [rbp - 704]
  movsd xmm8, [rbp - 712]
  movsd xmm9, [rbp - 720]
  movsd xmm10, [rbp - 728]
  movsd xmm11, [rbp - 736]
  movsd xmm12, [rbp - 744]
  movsd xmm13, [rbp - 752]
  movsd xmm14, [rbp - 760]
  movsd xmm15, [rbp - 768]
  movsd [rbp - 792], xmm15
  movsd xmm15, [rbp - 776]
  movsd [rbp - 800], xmm15
  movsd xmm15, [rbp - 784]
  movsd [rbp - 808], xmm15
  movsd [rbp - 816], xmm0
  movsd [rbp - 824], xmm1
  movsd xmm0, [rbp - 648]
  movsd xmm1, [rbp - 656]
  jmp .Lb6_6
.Lx6_7:
  mov rsi, rbx
  mov rdi, r12
  mov r8, r13
  mov r9, r14
  mov r10, r15
  mov rbx, [rbp - 136]
  mov r12, [rbp - 144]
  mov r13, [rbp - 152]
  movsd xmm0, [rbp - 648]
  movsd xmm1, [rbp - 656]
  movsd xmm2, [rbp - 664]
  movsd xmm3, [rbp - 672]
  movsd xmm4, [rbp - 680]
  movsd xmm5, [rbp - 688]
  movsd xmm6, [rbp - 696]
  movsd xmm7, [rbp - 704]
  movsd xmm8, [rbp - 712]
  movsd xmm9, [rbp - 720]
  movsd xmm10, [rbp - 728]
  movsd xmm11, [rbp - 736]
  movsd xmm12, [rbp - 744]
  movsd xmm13, [rbp - 752]
  movsd xmm14, [rbp - 760]
  movsd xmm15, [rbp - 768]
  movsd [rbp - 1328], xmm15
  movsd xmm15, [rbp - 776]
  movsd [rbp - 1336], xmm15
  jmp .Lb6_10
.Lb6_6:
  mov r11, r15
  imul r11, rbx
  mov [rbp - 168], r11
  mov r11, [rbp - 168]
  add r11, r14
  mov [rbp - 176], r11
  mov r11, r9
  mov rax, [rbp - 176]
  imul rax, rax, 8
  add r11, rax
  mov [rbp - 184], r11
  mov rax, [rbp - 184]
  movsd xmm15, [rax]
  movsd [rbp - 832], xmm15
  movsd xmm15, [rbp - 824]
  xor eax, eax
  ucomisd xmm15, [rbp - 832]
  setp r11b
  seta al
  xor r11b, 1
  and al, r11b
  movzx eax, al
  mov [rbp - 192], rax
  mov r11, [rbp - 192]
  test r11, r11
  je .Lx6_8
  mov r11, [rbp - 184]
  mov [rbp - 200], r11
  mov r11, [rbp - 176]
  mov [rbp - 208], r11
  movsd xmm15, [rbp - 792]
  movsd [rbp - 840], xmm15
  movsd xmm15, [rbp - 800]
  movsd [rbp - 848], xmm15
  movsd xmm15, [rbp - 808]
  movsd [rbp - 856], xmm15
  movsd xmm15, [rbp - 816]
  movsd [rbp - 864], xmm15
  movsd xmm15, [rbp - 824]
  movsd [rbp - 872], xmm15
  jmp .Lb6_7
.Lx6_8:
  movsd xmm15, [rbp - 792]
  movsd [rbp - 1328], xmm15
  movsd xmm15, [rbp - 800]
  movsd [rbp - 1336], xmm15
  jmp .Lb6_10
.Lb6_7:
  mov rax, [rbp - 200]
  movsd xmm15, [rbp - 872]
  movsd [rax], xmm15
  movsd xmm15, xmm14
  mulsd xmm15, xmm5
  movsd [rbp - 880], xmm15
  movsd xmm15, [rbp - 856]
  mulsd xmm15, [rbp - 880]
  movsd [rbp - 888], xmm15
  movsd xmm15, xmm2
  mulsd xmm15, xmm14
  movsd [rbp - 896], xmm15
  movsd xmm15, [rbp - 896]
  mulsd xmm15, [rbp - 864]
  movsd [rbp - 904], xmm15
  movsd xmm15, xmm3
  mulsd xmm15, [rbp - 840]
  movsd [rbp - 912], xmm15
  movsd xmm15, xmm2
  mulsd xmm15, [rbp - 840]
  movsd [rbp - 920], xmm15
  movsd xmm15, xmm14
  mulsd xmm15, xmm3
  movsd [rbp - 928], xmm15
  movsd xmm15, [rbp - 928]
  mulsd xmm15, [rbp - 864]
  movsd [rbp - 936], xmm15
  movsd xmm15, [rbp - 920]
  subsd xmm15, [rbp - 936]
  movsd [rbp - 944], xmm15
  movsd xmm15, xmm4
  mulsd xmm15, [rbp - 944]
  movsd [rbp - 952], xmm15
  movsd xmm15, [rbp - 888]
  subsd xmm15, [rbp - 904]
  movsd [rbp - 960], xmm15
  movsd xmm15, [rbp - 960]
  subsd xmm15, [rbp - 912]
  movsd [rbp - 968], xmm15
  movsd xmm15, [rbp - 968]
  addsd xmm15, [rbp - 952]
  movsd [rbp - 976], xmm15
  movsd xmm15, [rbp - 976]
  xor eax, eax
  ucomisd xmm15, [rbp - 336]
  setp r11b
  seta al
  xor r11b, 1
  and al, r11b
  movzx eax, al
  mov r14, rax
  movsd xmm15, [rbp - 336]
  movsd [rbp - 984], xmm15
  mov r11, r14
  test r11, r11
  je .Lx6_9
  movsd xmm15, [rbp - 976]
  movsd [rbp - 984], xmm15
.Lx6_9:
  movsd xmm15, [rbp - 984]
  mulsd xmm15, [rbp - 400]
  movsd [rbp - 992], xmm15
  movsd xmm15, [rbp - 992]
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx6_11
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx6_10
  jb .Lx6_11
  mov r11, 0x7fffffffffffffff
  jmp .Lx6_11
.Lx6_10:
  xor r11d, r11d
.Lx6_11:
  mov r14, r11
  mov r11, r14
  mov rax, [rbp - 104]
  cmp r11, rax
  setg al
  movzx eax, al
  mov r15, rax
  mov r11, r14
  mov [rbp - 216], r11
  mov r11, r15
  test r11, r11
  je .Lx6_12
  mov r11, [rbp - 104]
  mov [rbp - 216], r11
.Lx6_12:
  mov r11, r10
  mov rax, [rbp - 216]
  add r11, rax
  mov r14, r11
  mov rax, r14
  movzx r11d, BYTE PTR [rax]
  mov r15, r11
  mov r11, rsi
  mov rax, [rbp - 208]
  add r11, rax
  mov r14, r11
  mov rax, r14
  mov r11, r15
  mov [rax], r11b
  mov r11, r13
  mov rax, [rbp - 80]
  cmp r11, rax
  sete al
  movzx eax, al
  mov r14, rax
  mov r11, r14
  test r11, r11
  je .Lx6_13
  mov r14, r9
  mov r15, r10
  mov [rbp - 224], rbx
  mov [rbp - 232], r12
  mov [rbp - 240], r13
  mov r11, [rbp - 208]
  mov [rbp - 248], r11
  mov rbx, rsi
  mov r12, rdi
  mov r13, r8
  movsd [rbp - 1000], xmm0
  movsd [rbp - 1008], xmm1
  movsd [rbp - 1016], xmm2
  movsd [rbp - 1024], xmm3
  movsd [rbp - 1032], xmm4
  movsd [rbp - 1040], xmm5
  movsd [rbp - 1048], xmm6
  movsd [rbp - 1056], xmm7
  movsd [rbp - 1064], xmm8
  movsd [rbp - 1072], xmm9
  movsd [rbp - 1080], xmm10
  movsd [rbp - 1088], xmm11
  movsd [rbp - 1096], xmm12
  movsd [rbp - 1104], xmm13
  movsd [rbp - 1112], xmm14
  movsd xmm15, [rbp - 840]
  movsd [rbp - 1120], xmm15
  movsd xmm15, [rbp - 848]
  movsd [rbp - 1128], xmm15
  movsd xmm15, [rbp - 984]
  movsd [rbp - 1136], xmm15
  jmp .Lb6_8
.Lx6_13:
  mov r14, r9
  mov r15, r10
  mov [rbp - 256], rbx
  mov [rbp - 264], r12
  mov [rbp - 272], r13
  mov r11, [rbp - 208]
  mov [rbp - 280], r11
  mov rbx, rsi
  mov r12, rdi
  mov r13, r8
  movsd [rbp - 1168], xmm0
  movsd [rbp - 1176], xmm1
  movsd [rbp - 1184], xmm2
  movsd [rbp - 1192], xmm3
  movsd [rbp - 1200], xmm4
  movsd [rbp - 1208], xmm5
  movsd [rbp - 1216], xmm6
  movsd [rbp - 1224], xmm7
  movsd [rbp - 1232], xmm8
  movsd [rbp - 1240], xmm9
  movsd [rbp - 1248], xmm10
  movsd [rbp - 1256], xmm11
  movsd [rbp - 1264], xmm12
  movsd [rbp - 1272], xmm13
  movsd [rbp - 1280], xmm14
  movsd xmm15, [rbp - 840]
  movsd [rbp - 1288], xmm15
  movsd xmm15, [rbp - 848]
  movsd [rbp - 1296], xmm15
  movsd xmm15, [rbp - 984]
  movsd [rbp - 1304], xmm15
  jmp .Lb6_9
.Lb6_8:
  movsd xmm15, [rbp - 1000]
  addsd xmm15, [rbp - 1072]
  movsd [rbp - 1144], xmm15
  movsd xmm0, [rbp - 1144]
  call sin
  movsd xmm15, xmm0
  mulsd xmm15, [rbp - 352]
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  addsd xmm15, [rbp - 352]
  movsd [rbp - 1152], xmm15
  movsd xmm15, [rbp - 1144]
  mulsd xmm15, [rbp - 432]
  movsd xmm0, xmm15
  call cos
  movsd xmm1, xmm0
  movsd xmm15, xmm1
  mulsd xmm15, [rbp - 352]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  addsd xmm15, [rbp - 352]
  movsd [rbp - 1160], xmm15
  movsd xmm15, [rbp - 1144]
  mulsd xmm15, [rbp - 440]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  addsd xmm15, [rbp - 448]
  movsd xmm1, xmm15
  movsd xmm0, xmm1
  call sin
  movsd xmm15, xmm0
  mulsd xmm15, [rbp - 352]
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  addsd xmm15, [rbp - 352]
  movsd xmm0, xmm15
  movsd xmm15, [rbp - 1136]
  mulsd xmm15, [rbp - 408]
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  addsd xmm15, [rbp - 416]
  movsd xmm2, xmm15
  movsd xmm15, [rbp - 1152]
  mulsd xmm15, xmm2
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  mulsd xmm15, [rbp - 424]
  movsd xmm3, xmm15
  movsd xmm15, xmm3
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx6_15
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx6_14
  jb .Lx6_15
  mov r11, 0x7fffffffffffffff
  jmp .Lx6_15
.Lx6_14:
  xor r11d, r11d
.Lx6_15:
  mov rax, 2147483647
  cmp r11, rax
  cmovg r11, rax
  mov rax, -2147483648
  cmp r11, rax
  cmovl r11, rax
  shl r11, 32
  shr r11, 32
  mov rsi, r11
  movsd xmm15, [rbp - 1160]
  mulsd xmm15, xmm2
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  mulsd xmm15, [rbp - 424]
  movsd xmm3, xmm15
  movsd xmm15, xmm3
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx6_17
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx6_16
  jb .Lx6_17
  mov r11, 0x7fffffffffffffff
  jmp .Lx6_17
.Lx6_16:
  xor r11d, r11d
.Lx6_17:
  mov rax, 2147483647
  cmp r11, rax
  cmovg r11, rax
  mov rax, -2147483648
  cmp r11, rax
  cmovl r11, rax
  shl r11, 32
  shr r11, 32
  mov rdi, r11
  movsd xmm15, xmm0
  mulsd xmm15, xmm2
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  mulsd xmm15, [rbp - 424]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx6_19
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx6_18
  jb .Lx6_19
  mov r11, 0x7fffffffffffffff
  jmp .Lx6_19
.Lx6_18:
  xor r11d, r11d
.Lx6_19:
  mov rax, 2147483647
  cmp r11, rax
  cmovg r11, rax
  mov rax, -2147483648
  cmp r11, rax
  cmovl r11, rax
  shl r11, 32
  shr r11, 32
  mov r8, r11
  mov r11, rsi
  shl r11d, 16
  shl r11, 32
  shr r11, 32
  mov r9, r11
  mov r11, rdi
  shl r11d, 8
  shl r11, 32
  shr r11, 32
  mov rsi, r11
  mov r11, r9
  or r11d, esi
  shl r11, 32
  shr r11, 32
  mov rdi, r11
  mov r11, rdi
  or r11d, r8d
  shl r11, 32
  shr r11, 32
  mov rsi, r11
  mov r11, r12
  mov rax, [rbp - 248]
  imul rax, rax, 4
  add r11, rax
  mov rdi, r11
  mov rax, rdi
  mov r11, rsi
  mov [rax], r11d
  mov rsi, rbx
  mov rdi, r12
  mov r8, r13
  mov r9, r14
  mov r10, r15
  mov rbx, [rbp - 224]
  mov r12, [rbp - 232]
  mov r13, [rbp - 240]
  movsd xmm0, [rbp - 1000]
  movsd xmm1, [rbp - 1008]
  movsd xmm2, [rbp - 1016]
  movsd xmm3, [rbp - 1024]
  movsd xmm4, [rbp - 1032]
  movsd xmm5, [rbp - 1040]
  movsd xmm6, [rbp - 1048]
  movsd xmm7, [rbp - 1056]
  movsd xmm8, [rbp - 1064]
  movsd xmm9, [rbp - 1072]
  movsd xmm10, [rbp - 1080]
  movsd xmm11, [rbp - 1088]
  movsd xmm12, [rbp - 1096]
  movsd xmm13, [rbp - 1104]
  movsd xmm14, [rbp - 1112]
  movsd xmm15, [rbp - 1120]
  movsd [rbp - 1328], xmm15
  movsd xmm15, [rbp - 1128]
  movsd [rbp - 1336], xmm15
  jmp .Lb6_10
.Lb6_9:
  movsd xmm15, [rbp - 1240]
  mulsd xmm15, [rbp - 456]
  movsd xmm0, xmm15
  movsd xmm15, [rbp - 1168]
  subsd xmm15, xmm0
  movsd [rbp - 1312], xmm15
  movsd xmm0, [rbp - 1312]
  call sin
  movsd xmm15, xmm0
  mulsd xmm15, [rbp - 464]
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  addsd xmm15, [rbp - 472]
  movsd [rbp - 1320], xmm15
  movsd xmm15, [rbp - 1312]
  mulsd xmm15, [rbp - 448]
  movsd xmm0, xmm15
  call cos
  movsd xmm1, xmm0
  movsd xmm15, xmm1
  mulsd xmm15, [rbp - 416]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  addsd xmm15, [rbp - 416]
  movsd xmm1, xmm15
  movsd xmm15, [rbp - 1304]
  mulsd xmm15, [rbp - 480]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  addsd xmm15, [rbp - 488]
  movsd xmm2, xmm15
  movsd xmm15, xmm2
  mulsd xmm15, [rbp - 424]
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx6_21
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx6_20
  jb .Lx6_21
  mov r11, 0x7fffffffffffffff
  jmp .Lx6_21
.Lx6_20:
  xor r11d, r11d
.Lx6_21:
  mov rax, 2147483647
  cmp r11, rax
  cmovg r11, rax
  mov rax, -2147483648
  cmp r11, rax
  cmovl r11, rax
  shl r11, 32
  shr r11, 32
  mov rsi, r11
  movsd xmm15, [rbp - 1320]
  mulsd xmm15, xmm2
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  mulsd xmm15, [rbp - 424]
  movsd xmm3, xmm15
  movsd xmm15, xmm3
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx6_23
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx6_22
  jb .Lx6_23
  mov r11, 0x7fffffffffffffff
  jmp .Lx6_23
.Lx6_22:
  xor r11d, r11d
.Lx6_23:
  mov rax, 2147483647
  cmp r11, rax
  cmovg r11, rax
  mov rax, -2147483648
  cmp r11, rax
  cmovl r11, rax
  shl r11, 32
  shr r11, 32
  mov rdi, r11
  movsd xmm15, xmm1
  mulsd xmm15, xmm2
  movsd xmm0, xmm15
  movsd xmm15, xmm0
  mulsd xmm15, [rbp - 424]
  movsd xmm1, xmm15
  movsd xmm15, xmm1
  cvttsd2si r11, xmm15
  mov rax, -9223372036854775808
  cmp r11, rax
  jne .Lx6_25
  ucomisd xmm15, [rip + __krell_zero]
  jp .Lx6_24
  jb .Lx6_25
  mov r11, 0x7fffffffffffffff
  jmp .Lx6_25
.Lx6_24:
  xor r11d, r11d
.Lx6_25:
  mov rax, 2147483647
  cmp r11, rax
  cmovg r11, rax
  mov rax, -2147483648
  cmp r11, rax
  cmovl r11, rax
  shl r11, 32
  shr r11, 32
  mov r8, r11
  mov r11, rsi
  shl r11d, 16
  shl r11, 32
  shr r11, 32
  mov r9, r11
  mov r11, rdi
  shl r11d, 8
  shl r11, 32
  shr r11, 32
  mov rsi, r11
  mov r11, r9
  or r11d, esi
  shl r11, 32
  shr r11, 32
  mov rdi, r11
  mov r11, rdi
  or r11d, r8d
  shl r11, 32
  shr r11, 32
  mov rsi, r11
  mov r11, r12
  mov rax, [rbp - 280]
  imul rax, rax, 4
  add r11, rax
  mov rdi, r11
  mov rax, rdi
  mov r11, rsi
  mov [rax], r11d
  mov rsi, rbx
  mov rdi, r12
  mov r8, r13
  mov r9, r14
  mov r10, r15
  mov rbx, [rbp - 256]
  mov r12, [rbp - 264]
  mov r13, [rbp - 272]
  movsd xmm0, [rbp - 1168]
  movsd xmm1, [rbp - 1176]
  movsd xmm2, [rbp - 1184]
  movsd xmm3, [rbp - 1192]
  movsd xmm4, [rbp - 1200]
  movsd xmm5, [rbp - 1208]
  movsd xmm6, [rbp - 1216]
  movsd xmm7, [rbp - 1224]
  movsd xmm8, [rbp - 1232]
  movsd xmm9, [rbp - 1240]
  movsd xmm10, [rbp - 1248]
  movsd xmm11, [rbp - 1256]
  movsd xmm12, [rbp - 1264]
  movsd xmm13, [rbp - 1272]
  movsd xmm14, [rbp - 1280]
  movsd xmm15, [rbp - 1288]
  movsd [rbp - 1328], xmm15
  movsd xmm15, [rbp - 1296]
  movsd [rbp - 1336], xmm15
  jmp .Lb6_10
.Lb6_10:
  movsd xmm15, xmm0
  addsd xmm15, [rbp - 392]
  movsd [rbp - 1344], xmm15
  movsd xmm0, [rbp - 1344]
  movsd xmm15, [rbp - 1328]
  movsd [rbp - 632], xmm15
  movsd xmm15, [rbp - 1336]
  movsd [rbp - 640], xmm15
  jmp .Lb6_3
.Lb6_11:
  mov rbx, [rbp - 16]
  mov r12, [rbp - 24]
  mov r13, [rbp - 32]
  mov r14, [rbp - 40]
  mov r15, [rbp - 48]
  leave
  ret
.size render_ring, .-render_ring
.globl render_frame
.type render_frame, @function
render_frame:
  push rbp
  mov rbp, rsp
  sub rsp, 960
  mov [rbp - 16], rbx
  mov [rbp - 24], r12
  mov [rbp - 32], r13
  mov [rbp - 40], r14
  mov [rbp - 48], r15
  mov rbx, rdi
  mov r12, rsi
  mov r13, rdx
  mov r14, rcx
  mov r15, r8
  mov [rbp - 56], r9
  mov r11, [rbp + 16]
  mov [rbp - 64], r11
  mov r11, [rbp + 24]
  mov [rbp - 72], r11
.Lb7_0:
  mov r11, 0
  mov [rbp - 80], r11
  mov r11, 1
  mov [rbp - 88], r11
  mov r11, 2
  mov [rbp - 96], r11
  mov r11, 3
  mov [rbp - 104], r11
  mov r11, 4
  mov [rbp - 112], r11
  mov r11, 5
  mov [rbp - 120], r11
  mov r11, 6
  mov rsi, r11
  mov r11, 10
  shl r11, 56
  shr r11, 56
  mov [rbp - 128], r11
  mov r11, 11
  mov [rbp - 136], r11
  mov r11, 17
  mov [rbp - 144], r11
  mov r11, 19
  mov [rbp - 152], r11
  mov r11, 21
  mov [rbp - 160], r11
  mov r11, 23
  mov [rbp - 168], r11
  mov r11, 26
  mov [rbp - 176], r11
  mov r11, 40
  mov [rbp - 184], r11
  mov r11, 43
  shl r11, 56
  shr r11, 56
  mov [rbp - 192], r11
  mov r11, 45
  shl r11, 56
  shr r11, 56
  mov [rbp - 200], r11
  mov r11, 46
  mov [rbp - 208], r11
  mov r11, 48
  shl r11, 56
  shr r11, 56
  mov [rbp - 216], r11
  mov r11, 61
  shl r11, 56
  shr r11, 56
  mov [rbp - 224], r11
  mov r11, 65
  mov [rbp - 232], r11
  mov r11, 72
  shl r11, 56
  shr r11, 56
  mov rsi, r11
  mov r11, 91
  shl r11, 56
  shr r11, 56
  mov [rbp - 240], r11
  mov r11, 109
  shl r11, 56
  shr r11, 56
  mov [rbp - 248], r11
  mov r11, 124
  shl r11, 56
  shr r11, 56
  mov [rbp - 256], r11
  mov r11, 27
  shl r11, 56
  shr r11, 56
  mov [rbp - 264], r11
  mov r11, 32
  shl r11, 56
  shr r11, 56
  mov [rbp - 272], r11
  mov r11, -1
  shl r11, 32
  shr r11, 32
  mov [rbp - 280], r11
  mov r11, 58879
  shl r11, 32
  shr r11, 32
  mov [rbp - 288], r11
  mov r11, 329744
  shl r11, 32
  shr r11, 32
  mov [rbp - 296], r11
  mov r11, 12615935
  shl r11, 32
  shr r11, 32
  mov [rbp - 304], r11
  mov r11, 16756768
  shl r11, 32
  shr r11, 32
  mov [rbp - 312], r11
  mov r11, rbx
  mov rax, [rbp - 80]
  add r11, rax
  mov rdi, r11
  mov rax, rdi
  mov r11, [rbp - 264]
  mov [rax], r11b
  mov r11, rbx
  mov rax, [rbp - 88]
  add r11, rax
  mov rdi, r11
  mov rax, rdi
  mov r11, [rbp - 240]
  mov [rax], r11b
  mov r11, rbx
  mov rax, [rbp - 96]
  add r11, rax
  mov rdi, r11
  mov rax, rdi
  mov r11, rsi
  mov [rax], r11b
  mov r11, 0
  shl r11, 32
  shr r11, 32
  mov [rbp - 320], r11
  mov rdi, rbx
  mov rsi, [rbp - 104]
  mov rdx, [rbp - 288]
  mov rcx, [rbp - 320]
  call put_color
  mov rsi, rax
  mov r11, 1
  shl r11, 32
  shr r11, 32
  mov [rbp - 328], r11
  mov rdi, rbx
  mov rdx, [rbp - 296]
  mov rcx, [rbp - 328]
  call put_color
  mov [rbp - 336], rax
  mov rdi, rbx
  mov rsi, [rbp - 336]
  mov rdx, [rbp - 192]
  mov rcx, [rbp - 224]
  mov r8, [rbp - 192]
  mov r9, r15
  call make_line
  mov [rbp - 344], rax
  lea r11, [rip + __krell_data_1]
  mov rsi, r11
  mov r11, rbx
  mov rax, [rbp - 336]
  add r11, rax
  mov rdi, r11
  mov r11, rdi
  mov rax, [rbp - 104]
  add r11, rax
  mov r8, r11
  mov rdi, r8
  mov rdx, [rbp - 160]
  call copy_bytes
  mov r11, r15
  mov rax, [rbp - 232]
  cmp r11, rax
  setge al
  movzx eax, al
  mov rsi, rax
  mov r11, rsi
  test r11, r11
  je .Lx7_1
  mov rsi, [rbp - 336]
  mov [rbp - 352], r14
  mov r11, [rbp - 56]
  mov [rbp - 360], r11
  mov r11, [rbp - 64]
  mov [rbp - 368], r11
  mov r11, [rbp - 72]
  mov [rbp - 376], r11
  mov r14, r12
  mov r12, r15
  mov r15, r13
  mov r13, [rbp - 344]
  jmp .Lb7_1
.Lx7_1:
  mov rsi, [rbp - 344]
  mov r11, [rbp - 56]
  mov [rbp - 384], r11
  mov r11, [rbp - 64]
  mov [rbp - 392], r11
  mov r11, [rbp - 72]
  mov [rbp - 400], r11
  mov r11, r15
  mov r15, r14
  mov r14, r13
  mov r13, r12
  mov r12, r11
  jmp .Lb7_2
.Lb7_1:
  lea r11, [rip + __krell_data_2]
  mov rdi, r11
  mov r11, r12
  sub r11, [rbp - 176]
  mov r8, r11
  mov r11, rbx
  mov rax, rsi
  add r11, rax
  mov r9, r11
  mov r11, r9
  mov rax, r8
  add r11, rax
  mov rsi, r11
  mov rdx, [rbp - 168]
  mov r11, rsi
  mov rsi, rdi
  mov rdi, r11
  call copy_bytes
  mov rsi, r13
  mov r13, r14
  mov r14, r15
  mov r15, [rbp - 352]
  mov r11, [rbp - 360]
  mov [rbp - 384], r11
  mov r11, [rbp - 368]
  mov [rbp - 392], r11
  mov r11, [rbp - 376]
  mov [rbp - 400], r11
  jmp .Lb7_2
.Lb7_2:
  mov rdi, rbx
  mov rdx, [rbp - 304]
  mov rcx, [rbp - 320]
  call put_color
  mov [rbp - 408], rax
  mov rdi, rbx
  mov rsi, [rbp - 408]
  mov rdx, [rbp - 256]
  mov rcx, [rbp - 272]
  mov r8, [rbp - 256]
  mov r9, r12
  call make_line
  mov rsi, rax
  lea r11, [rip + __krell_data_3]
  mov rdi, r11
  mov r11, rbx
  mov rax, [rbp - 408]
  add r11, rax
  mov r8, r11
  mov r11, r8
  mov rax, [rbp - 96]
  add r11, rax
  mov r9, r11
  mov r11, r12
  sub r11, [rbp - 112]
  mov r8, r11
  mov r11, r8
  mov rax, [rbp - 232]
  cmp r11, rax
  setg al
  movzx eax, al
  mov r10, rax
  mov r11, r8
  mov [rbp - 416], r11
  mov r11, r10
  test r11, r11
  je .Lx7_2
  mov r11, [rbp - 232]
  mov [rbp - 416], r11
.Lx7_2:
  mov r11, [rbp - 416]
  mov rax, [rbp - 80]
  cmp r11, rax
  setg al
  movzx eax, al
  mov r8, rax
  mov r11, r8
  test r11, r11
  je .Lx7_3
  mov r8, [rbp - 416]
  mov [rbp - 424], r15
  mov r11, [rbp - 384]
  mov [rbp - 432], r11
  mov r11, [rbp - 392]
  mov [rbp - 440], r11
  mov r11, [rbp - 400]
  mov [rbp - 448], r11
  mov r15, r14
  mov r14, r13
  mov r13, r12
  mov r12, rsi
  mov rsi, r9
  jmp .Lb7_3
.Lx7_3:
  mov r11, [rbp - 384]
  mov [rbp - 456], r11
  mov r11, [rbp - 392]
  mov [rbp - 464], r11
  mov r11, [rbp - 400]
  mov [rbp - 472], r11
  jmp .Lb7_4
.Lb7_3:
  mov rdx, r8
  mov r11, rsi
  mov rsi, rdi
  mov rdi, r11
  call copy_bytes
  mov rsi, r12
  mov r12, r13
  mov r13, r14
  mov r14, r15
  mov r15, [rbp - 424]
  mov r11, [rbp - 432]
  mov [rbp - 456], r11
  mov r11, [rbp - 440]
  mov [rbp - 464], r11
  mov r11, [rbp - 448]
  mov [rbp - 472], r11
  jmp .Lb7_4
.Lb7_4:
  mov rdi, rbx
  mov rdx, [rbp - 288]
  mov rcx, [rbp - 320]
  call put_color
  mov rdi, rax
  mov rsi, rdi
  mov rdx, [rbp - 192]
  mov rcx, [rbp - 200]
  mov r8, [rbp - 192]
  mov r9, r12
  mov rdi, rbx
  call make_line
  mov rsi, rax
  mov rdi, rsi
  mov r8, r13
  mov r9, r14
  mov r10, r15
  mov r13, [rbp - 464]
  mov r14, [rbp - 472]
  mov rsi, rbx
  mov rbx, r12
  mov r12, [rbp - 456]
  jmp .Lb7_5
.Lb7_5:
  mov r15, r12
  mov [rbp - 480], r13
  mov [rbp - 488], r14
  mov r12, r9
  mov r13, r10
  mov r14, rbx
  mov r9, [rbp - 280]
  mov r10, rsi
  mov rbx, r8
  mov rsi, [rbp - 80]
  mov r8, [rbp - 280]
  jmp .Lb7_6
.Lb7_6:
  mov r11, rsi
  mov rax, [rbp - 480]
  cmp r11, rax
  setge al
  movzx eax, al
  mov [rbp - 496], rax
  mov r11, [rbp - 496]
  test r11, r11
  je .Lx7_4
  mov rsi, rdi
  mov rbx, r10
  mov r12, r14
  mov rdi, r15
  mov r8, [rbp - 480]
  mov r13, [rbp - 488]
  jmp .Lb7_14
.Lx7_4:
  mov [rbp - 504], r15
  mov r11, [rbp - 480]
  mov [rbp - 512], r11
  mov r11, [rbp - 488]
  mov [rbp - 520], r11
  mov r15, r14
  mov r14, r13
  mov r13, r12
  mov r12, rbx
  mov rbx, r10
  mov r10, r9
  mov r9, r8
  mov r8, rdi
  mov rdi, rsi
  mov rsi, [rbp - 80]
  jmp .Lb7_7
.Lb7_7:
  mov r11, rsi
  mov rax, r15
  cmp r11, rax
  setge al
  movzx eax, al
  mov [rbp - 528], rax
  mov r11, [rbp - 528]
  test r11, r11
  je .Lx7_5
  mov rsi, rdi
  mov rdi, r8
  mov r8, r9
  mov r9, r10
  mov r10, rbx
  mov rbx, r12
  mov r12, r13
  mov r13, r14
  mov r14, r15
  mov r15, [rbp - 504]
  mov r11, [rbp - 512]
  mov [rbp - 536], r11
  mov r11, [rbp - 520]
  mov [rbp - 544], r11
  jmp .Lb7_8
.Lx7_5:
  mov r11, [rbp - 504]
  mov [rbp - 568], r11
  mov r11, [rbp - 512]
  mov [rbp - 576], r11
  mov r11, [rbp - 520]
  mov [rbp - 584], r11
  jmp .Lb7_9
.Lb7_8:
  mov r11, r10
  mov rax, rdi
  add r11, rax
  mov [rbp - 552], r11
  mov rax, [rbp - 552]
  mov r11, [rbp - 128]
  mov [rax], r11b
  mov r11, rdi
  add r11, [rbp - 88]
  mov [rbp - 560], r11
  mov r11, rsi
  add r11, [rbp - 88]
  mov rdi, r11
  mov rsi, rdi
  mov rdi, [rbp - 560]
  mov r11, [rbp - 536]
  mov [rbp - 480], r11
  mov r11, [rbp - 544]
  mov [rbp - 488], r11
  jmp .Lb7_6
.Lb7_9:
  mov r11, rdi
  imul r11, r15
  mov [rbp - 592], r11
  mov r11, [rbp - 592]
  add r11, rsi
  mov [rbp - 600], r11
  mov r11, r12
  mov rax, [rbp - 600]
  add r11, rax
  mov [rbp - 608], r11
  mov rax, [rbp - 608]
  movzx r11d, BYTE PTR [rax]
  mov [rbp - 616], r11
  mov r11, r13
  mov rax, [rbp - 600]
  imul rax, rax, 4
  add r11, rax
  mov [rbp - 624], r11
  mov rax, [rbp - 624]
  mov r11d, DWORD PTR [rax]
  mov [rbp - 632], r11
  mov r11, r14
  mov rax, [rbp - 600]
  imul rax, rax, 4
  add r11, rax
  mov [rbp - 640], r11
  mov rax, [rbp - 640]
  mov r11d, DWORD PTR [rax]
  mov [rbp - 648], r11
  mov r11, [rbp - 632]
  mov rax, r9
  cmp r11, rax
  setne al
  movzx eax, al
  mov [rbp - 656], rax
  mov r11, [rbp - 656]
  test r11, r11
  je .Lx7_6
  mov [rbp - 664], r12
  mov [rbp - 672], r13
  mov [rbp - 680], r14
  mov [rbp - 688], r15
  mov r11, [rbp - 568]
  mov [rbp - 696], r11
  mov r11, [rbp - 576]
  mov [rbp - 704], r11
  mov r11, [rbp - 584]
  mov [rbp - 712], r11
  mov r11, [rbp - 648]
  mov [rbp - 720], r11
  mov r11, [rbp - 616]
  mov [rbp - 728], r11
  mov r12, rdi
  mov r13, [rbp - 632]
  mov r14, r10
  mov r15, rbx
  mov rbx, rsi
  mov rsi, r8
  jmp .Lb7_10
.Lx7_6:
  mov r11, [rbp - 568]
  mov [rbp - 736], r11
  mov r11, [rbp - 576]
  mov [rbp - 744], r11
  mov r11, [rbp - 584]
  mov [rbp - 752], r11
  mov r11, [rbp - 648]
  mov [rbp - 760], r11
  mov r11, [rbp - 616]
  mov [rbp - 768], r11
  jmp .Lb7_11
.Lb7_10:
  mov rdi, r15
  mov rdx, r13
  mov rcx, [rbp - 320]
  call put_color
  mov rdi, rax
  mov rsi, rbx
  mov r8, rdi
  mov r9, r13
  mov r10, r14
  mov rbx, r15
  mov r13, [rbp - 672]
  mov r14, [rbp - 680]
  mov r15, [rbp - 688]
  mov r11, [rbp - 696]
  mov [rbp - 736], r11
  mov r11, [rbp - 704]
  mov [rbp - 744], r11
  mov r11, [rbp - 712]
  mov [rbp - 752], r11
  mov r11, [rbp - 720]
  mov [rbp - 760], r11
  mov r11, [rbp - 728]
  mov [rbp - 768], r11
  mov rdi, r12
  mov r12, [rbp - 664]
  jmp .Lb7_11
.Lb7_11:
  mov r11, [rbp - 760]
  mov rax, r10
  cmp r11, rax
  setne al
  movzx eax, al
  mov [rbp - 776], rax
  mov r11, [rbp - 776]
  test r11, r11
  je .Lx7_7
  mov [rbp - 784], r12
  mov [rbp - 792], r13
  mov [rbp - 800], r14
  mov [rbp - 808], r15
  mov r11, [rbp - 736]
  mov [rbp - 816], r11
  mov r11, [rbp - 744]
  mov [rbp - 824], r11
  mov r11, [rbp - 752]
  mov [rbp - 832], r11
  mov r11, [rbp - 768]
  mov [rbp - 840], r11
  mov r12, rdi
  mov r13, r9
  mov r14, [rbp - 760]
  mov r15, rbx
  mov rbx, rsi
  mov rsi, r8
  jmp .Lb7_12
.Lx7_7:
  mov r11, [rbp - 736]
  mov [rbp - 848], r11
  mov r11, [rbp - 744]
  mov [rbp - 856], r11
  mov r11, [rbp - 752]
  mov [rbp - 864], r11
  mov r11, [rbp - 768]
  mov [rbp - 872], r11
  jmp .Lb7_13
.Lb7_12:
  mov rdi, r15
  mov rdx, r14
  mov rcx, [rbp - 328]
  call put_color
  mov rdi, rax
  mov rsi, rbx
  mov r8, rdi
  mov r9, r13
  mov r10, r14
  mov rbx, r15
  mov r13, [rbp - 792]
  mov r14, [rbp - 800]
  mov r15, [rbp - 808]
  mov r11, [rbp - 816]
  mov [rbp - 848], r11
  mov r11, [rbp - 824]
  mov [rbp - 856], r11
  mov r11, [rbp - 832]
  mov [rbp - 864], r11
  mov r11, [rbp - 840]
  mov [rbp - 872], r11
  mov rdi, r12
  mov r12, [rbp - 784]
  jmp .Lb7_13
.Lb7_13:
  mov r11, rbx
  mov rax, r8
  add r11, rax
  mov [rbp - 880], r11
  mov rax, [rbp - 880]
  mov r11, [rbp - 872]
  mov [rax], r11b
  mov r11, r8
  add r11, [rbp - 88]
  mov [rbp - 888], r11
  mov r11, rsi
  add r11, [rbp - 88]
  mov r8, r11
  mov rsi, r8
  mov r8, [rbp - 888]
  mov r11, [rbp - 848]
  mov [rbp - 504], r11
  mov r11, [rbp - 856]
  mov [rbp - 512], r11
  mov r11, [rbp - 864]
  mov [rbp - 520], r11
  jmp .Lb7_7
.Lb7_14:
  mov rdi, rbx
  mov rdx, [rbp - 288]
  mov rcx, [rbp - 320]
  call put_color
  mov rdi, rax
  mov rsi, rdi
  mov rdx, [rbp - 296]
  mov rcx, [rbp - 328]
  mov rdi, rbx
  call put_color
  mov rsi, rax
  mov rdi, rbx
  mov rdx, [rbp - 192]
  mov rcx, [rbp - 200]
  mov r8, [rbp - 192]
  mov r9, r12
  call make_line
  mov rdi, rax
  mov rsi, rdi
  mov rdx, [rbp - 312]
  mov rcx, [rbp - 320]
  mov rdi, rbx
  call put_color
  mov r14, rax
  mov rdi, rbx
  mov rsi, r14
  mov rdx, [rbp - 256]
  mov rcx, [rbp - 272]
  mov r8, [rbp - 256]
  mov r9, r12
  call make_line
  mov r15, rax
  lea r11, [rip + __krell_data_4]
  mov rsi, r11
  mov r11, rbx
  mov rax, r14
  add r11, rax
  mov [rbp - 896], r11
  mov r11, [rbp - 896]
  mov rax, [rbp - 96]
  add r11, rax
  mov rdi, r11
  mov r11, 9
  mov r8, r11
  mov rdx, r8
  call copy_bytes
  mov r11, [rbp - 896]
  mov rax, [rbp - 136]
  add r11, rax
  mov rsi, r11
  mov rdi, [rbp - 896]
  mov rsi, [rbp - 136]
  mov rdx, r13
  call put_digits6
  mov rsi, rax
  lea r11, [rip + __krell_data_5]
  mov rsi, r11
  mov r11, [rbp - 896]
  mov rax, [rbp - 144]
  add r11, rax
  mov rdi, r11
  mov r11, r12
  sub r11, [rbp - 152]
  mov r8, r11
  mov r11, r8
  mov rax, [rbp - 208]
  cmp r11, rax
  setg al
  movzx eax, al
  mov r9, rax
  mov r11, r8
  mov r10, r11
  mov r11, r9
  test r11, r11
  je .Lx7_8
  mov r11, [rbp - 208]
  mov r10, r11
.Lx7_8:
  mov r11, r10
  mov rax, [rbp - 80]
  cmp r11, rax
  setg al
  movzx eax, al
  mov r8, rax
  mov r11, r8
  test r11, r11
  je .Lx7_9
  mov r8, r10
  mov r13, r12
  mov r12, r15
  mov r11, rdi
  mov rdi, rsi
  mov rsi, r11
  jmp .Lb7_15
.Lx7_9:
  mov rsi, r15
  jmp .Lb7_16
.Lb7_15:
  mov rdx, r8
  mov r11, rsi
  mov rsi, rdi
  mov rdi, r11
  call copy_bytes
  mov rsi, r12
  mov r12, r13
  jmp .Lb7_16
.Lb7_16:
  mov rdi, rbx
  mov rdx, [rbp - 288]
  mov rcx, [rbp - 320]
  call put_color
  mov r13, rax
  mov rdi, rbx
  mov rsi, r13
  mov rdx, [rbp - 192]
  mov rcx, [rbp - 224]
  mov r8, [rbp - 192]
  mov r9, r12
  call make_line
  mov rsi, rax
  lea r11, [rip + __krell_data_6]
  mov rdi, r11
  mov r11, rbx
  mov rax, r13
  add r11, rax
  mov r8, r11
  mov r11, r8
  mov rax, [rbp - 104]
  add r11, rax
  mov r9, r11
  mov r11, r12
  sub r11, [rbp - 120]
  mov r8, r11
  mov r11, r8
  mov rax, [rbp - 184]
  cmp r11, rax
  setg al
  movzx eax, al
  mov r10, rax
  mov r11, r8
  mov r12, r11
  mov r11, r10
  test r11, r11
  je .Lx7_10
  mov r11, [rbp - 184]
  mov r12, r11
.Lx7_10:
  mov r11, r12
  mov rax, [rbp - 80]
  cmp r11, rax
  setg al
  movzx eax, al
  mov r8, rax
  mov r11, r8
  test r11, r11
  je .Lx7_11
  mov r8, r12
  mov r12, rsi
  mov rsi, r9
  jmp .Lb7_17
.Lx7_11:
  mov rdi, rsi
  mov rsi, rbx
  jmp .Lb7_18
.Lb7_17:
  mov rdx, r8
  mov r11, rsi
  mov rsi, rdi
  mov rdi, r11
  call copy_bytes
  mov rsi, rbx
  mov rdi, r12
  jmp .Lb7_18
.Lb7_18:
  mov r11, rsi
  mov rax, rdi
  add r11, rax
  mov r8, r11
  mov rax, r8
  mov r11, [rbp - 264]
  mov [rax], r11b
  mov r11, rdi
  add r11, [rbp - 88]
  mov r8, r11
  mov r11, rsi
  mov rax, r8
  add r11, rax
  mov rdi, r11
  mov rax, rdi
  mov r11, [rbp - 240]
  mov [rax], r11b
  mov r11, r8
  add r11, [rbp - 88]
  mov rdi, r11
  mov r11, rsi
  mov rax, rdi
  add r11, rax
  mov r8, r11
  mov rax, r8
  mov r11, [rbp - 216]
  mov [rax], r11b
  mov r11, rdi
  add r11, [rbp - 88]
  mov r8, r11
  mov r11, rsi
  mov rax, r8
  add r11, rax
  mov rdi, r11
  mov rax, rdi
  mov r11, [rbp - 248]
  mov [rax], r11b
  mov r11, r8
  add r11, [rbp - 88]
  mov rsi, r11
  mov rax, rsi
  mov rbx, [rbp - 16]
  mov r12, [rbp - 24]
  mov r13, [rbp - 32]
  mov r14, [rbp - 40]
  mov r15, [rbp - 48]
  leave
  ret
.size render_frame, .-render_frame
.globl main
.type main, @function
main:
  push rbp
  mov rbp, rsp
  sub rsp, 368
  mov [rbp - 16], rbx
  mov [rbp - 24], r12
  mov [rbp - 32], r13
  mov [rbp - 40], r14
  mov [rbp - 48], r15
.Lb8_0:
  mov r11, 0
  mov rbx, r11
  mov r11, 1
  mov r12, r11
  mov r11, 33000
  shl r11, 32
  shr r11, 32
  mov r13, r11
  mov r11, 8
  mov r14, r11
  mov rdi, r14
  call malloc
  mov r15, rax
  mov r11, 1
  shl r11, 32
  shr r11, 32
  mov [rbp - 56], r11
  mov r11, 21523
  mov rsi, r11
  mov rdi, [rbp - 56]
  mov rdx, r15
  call ioctl
  mov rdi, rax
  mov r11, r15
  mov rax, rbx
  imul rax, rax, 2
  add r11, rax
  mov rsi, r11
  mov r11, r15
  mov rax, r12
  imul rax, rax, 2
  add r11, rax
  mov rdi, r11
  mov rax, rsi
  movzx r11d, WORD PTR [rax]
  mov [rbp - 64], r11
  mov rax, rdi
  movzx r11d, WORD PTR [rax]
  mov [rbp - 72], r11
  mov rdi, r15
  call free
  mov r11, [rbp - 64]
  mov rsi, r11
  mov r11, [rbp - 72]
  mov rdi, r11
  mov r11, 40
  mov r8, r11
  mov r11, rdi
  mov rax, r8
  cmp r11, rax
  setl al
  movzx eax, al
  mov r9, rax
  mov r11, 80
  mov r8, r11
  mov r11, rdi
  mov r10, r11
  mov r11, r9
  test r11, r11
  je .Lx8_1
  mov r11, r8
  mov r10, r11
.Lx8_1:
  mov r11, 220
  mov rdi, r11
  mov r11, r10
  mov rax, rdi
  cmp r11, rax
  setg al
  movzx eax, al
  mov r8, rax
  mov r11, r10
  mov r15, r11
  mov r11, r8
  test r11, r11
  je .Lx8_2
  mov r11, rdi
  mov r15, r11
.Lx8_2:
  mov r11, 20
  mov rdi, r11
  mov r11, rsi
  mov rax, rdi
  cmp r11, rax
  setl al
  movzx eax, al
  mov r8, rax
  mov r11, 24
  mov rdi, r11
  mov r11, rsi
  mov r9, r11
  mov r11, r8
  test r11, r11
  je .Lx8_3
  mov r11, rdi
  mov r9, r11
.Lx8_3:
  mov r11, 70
  mov rsi, r11
  mov r11, r9
  mov rax, rsi
  cmp r11, rax
  setg al
  movzx eax, al
  mov rdi, rax
  mov r11, r9
  mov [rbp - 80], r11
  mov r11, rdi
  test r11, r11
  je .Lx8_4
  mov r11, rsi
  mov [rbp - 80], r11
.Lx8_4:
  mov r11, 6
  mov [rbp - 88], r11
  mov r11, [rbp - 80]
  sub r11, [rbp - 88]
  mov [rbp - 96], r11
  mov r11, r15
  imul r11, [rbp - 96]
  mov [rbp - 104], r11
  mov r11, 1048576
  mov rsi, r11
  mov rdi, rsi
  call malloc
  mov [rbp - 112], rax
  mov rdi, [rbp - 104]
  call malloc
  mov [rbp - 120], rax
  mov r11, 4
  mov [rbp - 128], r11
  mov r11, [rbp - 104]
  imul r11, [rbp - 128]
  mov [rbp - 136], r11
  mov rdi, [rbp - 136]
  call malloc
  mov [rbp - 144], rax
  mov rdi, [rbp - 136]
  call malloc
  mov [rbp - 152], rax
  mov r11, [rbp - 104]
  imul r11, r14
  mov rsi, r11
  mov rdi, rsi
  call malloc
  mov [rbp - 160], rax
  mov r11, 16
  mov rsi, r11
  mov rdi, rsi
  call malloc
  mov [rbp - 168], rax
  mov r11, [rbp - 168]
  mov rax, rbx
  add r11, rax
  mov rsi, r11
  mov r11, 27
  shl r11, 56
  shr r11, 56
  mov rdi, r11
  mov rax, rsi
  mov r11, rdi
  mov [rax], r11b
  mov r11, [rbp - 168]
  mov rax, r12
  add r11, rax
  mov rsi, r11
  mov r11, 91
  shl r11, 56
  shr r11, 56
  mov r8, r11
  mov rax, rsi
  mov r11, r8
  mov [rax], r11b
  mov r11, 2
  mov rsi, r11
  mov r11, [rbp - 168]
  mov rax, rsi
  add r11, rax
  mov r9, r11
  mov r11, 50
  shl r11, 56
  shr r11, 56
  mov rsi, r11
  mov rax, r9
  mov r11, rsi
  mov [rax], r11b
  mov r11, 3
  mov r9, r11
  mov r11, [rbp - 168]
  mov rax, r9
  add r11, rax
  mov r10, r11
  mov r11, 74
  shl r11, 56
  shr r11, 56
  mov r9, r11
  mov rax, r10
  mov r11, r9
  mov [rax], r11b
  mov r11, [rbp - 168]
  mov rax, [rbp - 128]
  add r11, rax
  mov r9, r11
  mov rax, r9
  mov r11, rdi
  mov [rax], r11b
  mov r11, 5
  mov rdi, r11
  mov r11, [rbp - 168]
  mov rax, rdi
  add r11, rax
  mov r9, r11
  mov rax, r9
  mov r11, r8
  mov [rax], r11b
  mov r11, [rbp - 168]
  mov rax, [rbp - 88]
  add r11, rax
  mov rdi, r11
  mov r11, 63
  shl r11, 56
  shr r11, 56
  mov r8, r11
  mov rax, rdi
  mov r11, r8
  mov [rax], r11b
  mov r11, 7
  mov rdi, r11
  mov r11, [rbp - 168]
  mov rax, rdi
  add r11, rax
  mov r8, r11
  mov rax, r8
  mov r11, rsi
  mov [rax], r11b
  mov r11, [rbp - 168]
  mov rax, r14
  add r11, rax
  mov rsi, r11
  mov r11, 53
  shl r11, 56
  shr r11, 56
  mov rdi, r11
  mov rax, rsi
  mov r11, rdi
  mov [rax], r11b
  mov r11, 9
  mov rsi, r11
  mov r11, [rbp - 168]
  mov rax, rsi
  add r11, rax
  mov rdi, r11
  mov r11, 108
  shl r11, 56
  shr r11, 56
  mov rsi, r11
  mov rax, rdi
  mov r11, rsi
  mov [rax], r11b
  mov r11, 10
  mov rsi, r11
  mov rdi, [rbp - 56]
  mov rdx, rsi
  mov rsi, [rbp - 168]
  call write
  mov rdi, rax
  mov rdi, [rbp - 168]
  call free
  lea r11, [rip + __krell_data_0]
  mov rsi, r11
  mov r14, rbx
  mov r11, [rbp - 120]
  mov [rbp - 176], r11
  mov r11, [rbp - 144]
  mov [rbp - 184], r11
  mov r11, [rbp - 152]
  mov [rbp - 192], r11
  mov r11, [rbp - 160]
  mov [rbp - 200], r11
  mov [rbp - 208], rsi
  mov [rbp - 216], r15
  mov r11, [rbp - 80]
  mov [rbp - 224], r11
  mov r11, [rbp - 96]
  mov [rbp - 232], r11
  mov r15, [rbp - 112]
  jmp .Lb8_1
.Lb8_1:
  mov r11, r14
  cvtsi2sd xmm15, r11
  movsd xmm0, xmm15
  mov rax, 0x3fa70a3d70a3d70a
  movq xmm15, rax
  movsd xmm1, xmm15
  movsd xmm15, xmm0
  mulsd xmm15, xmm1
  movsd [rbp - 240], xmm15
  mov rdi, [rbp - 176]
  mov rsi, [rbp - 184]
  mov rdx, [rbp - 192]
  mov rcx, [rbp - 200]
  mov r8, [rbp - 216]
  mov r9, [rbp - 232]
  movsd xmm0, [rbp - 240]
  call render_plasma
  mov rax, 0x3fe6666666666666
  movq xmm15, rax
  movsd xmm0, xmm15
  movsd xmm15, [rbp - 240]
  mulsd xmm15, xmm0
  movsd xmm1, xmm15
  mov rax, 0x3feccccccccccccd
  movq xmm15, rax
  movsd xmm0, xmm15
  movsd xmm15, [rbp - 240]
  mulsd xmm15, xmm0
  movsd xmm2, xmm15
  mov rax, 0x3fff333333333333
  movq xmm15, rax
  movsd xmm0, xmm15
  mov rax, 0x3fea3d70a3d70a3d
  movq xmm15, rax
  movsd xmm3, xmm15
  mov rax, 0x4014cccccccccccd
  movq xmm15, rax
  movsd [rbp - 248], xmm15
  mov r11, [rbp - 232]
  mov [rbp - 368], r11
  mov r11, rbx
  mov [rbp - 360], r11
  mov rdi, [rbp - 176]
  mov rsi, [rbp - 184]
  mov rdx, [rbp - 192]
  mov rcx, [rbp - 200]
  mov r8, [rbp - 208]
  mov r9, [rbp - 216]
  movsd xmm4, [rbp - 248]
  movsd xmm5, [rbp - 240]
  movsd xmm15, xmm1
  movsd xmm1, xmm2
  movsd xmm2, xmm0
  movsd xmm0, xmm15
  call render_ring
  mov rax, 0xbff3333333333333
  movq xmm15, rax
  movsd xmm0, xmm15
  movsd xmm15, [rbp - 240]
  mulsd xmm15, xmm0
  movsd xmm1, xmm15
  mov rax, 0x3ff6666666666666
  movq xmm15, rax
  movsd xmm0, xmm15
  movsd xmm15, [rbp - 240]
  mulsd xmm15, xmm0
  movsd xmm2, xmm15
  mov rax, 0x3ff0cccccccccccd
  movq xmm15, rax
  movsd xmm0, xmm15
  mov rax, 0x3fdae147ae147ae1
  movq xmm15, rax
  movsd xmm3, xmm15
  mov r11, [rbp - 232]
  mov [rbp - 368], r11
  mov r11, r12
  mov [rbp - 360], r11
  mov rdi, [rbp - 176]
  mov rsi, [rbp - 184]
  mov rdx, [rbp - 192]
  mov rcx, [rbp - 200]
  mov r8, [rbp - 208]
  mov r9, [rbp - 216]
  movsd xmm4, [rbp - 248]
  movsd xmm5, [rbp - 240]
  movsd xmm15, xmm1
  movsd xmm1, xmm2
  movsd xmm2, xmm0
  movsd xmm0, xmm15
  call render_ring
  mov r11, [rbp - 232]
  mov [rbp - 368], r11
  mov r11, r14
  mov [rbp - 360], r11
  mov rdi, r15
  mov rsi, [rbp - 176]
  mov rdx, [rbp - 184]
  mov rcx, [rbp - 192]
  mov r8, [rbp - 216]
  mov r9, [rbp - 224]
  call render_frame
  mov rsi, rax
  mov rdi, [rbp - 56]
  mov rdx, rsi
  mov rsi, r15
  call write
  mov rdi, rax
  mov rdi, r13
  call usleep
  mov rsi, rax
  mov r11, r14
  add r11, r12
  mov rsi, r11
  mov r14, rsi
  jmp .Lb8_1
.size main, .-main
.section .rodata
.balign 1
__krell_data_0:
  .quad 0x3d3b3a7e2d2c2e20
  .quad 0x4024232a21
.balign 1
__krell_data_1:
  .quad 0x4c4c45524b205b20
  .quad 0x31762045524f4320
  .quad 0x205d20302e
.balign 1
__krell_data_2:
  .quad 0x494843414d205b20
  .quad 0x4e4520524920454e
  .quad 0x205d20454e4947
.balign 1
__krell_data_3:
  .quad 0x4c42204153532020
  .quad 0x204752412d4b434f
  .quad 0x204c41544f54207c
  .quad 0x4349544e414d4553
  .quad 0x4255204f4e282053
  .quad 0x47524154207c2029
  .quad 0x5f363878203a5445
  .quad 0x564954414e203436
  .quad 0x45
.balign 1
__krell_data_4:
  .quad 0x3a454d4152462020
  .quad 0x20
.balign 1
__krell_data_5:
  .quad 0x4646494c43207c20
  .quad 0x455a207c2030203a
  .quad 0x204b41454c2d4f52
  .quad 0x435b207c20415353
  .quad 0x4f5420432b4c5254
  .quad 0x5d5449584520
.balign 1
__krell_data_6:
  .quad 0x544847494e205b20
  .quad 0x42414c2045524157
  .quad 0x54524f50203a205a
  .quad 0x53534120454c4241
  .quad 0x205d20594c424d45
.balign 16
__krell_s32: .long 0x80000000, 0, 0, 0
__krell_s64: .quad 0x8000000000000000, 0
__krell_a32: .long 0x7fffffff, 0, 0, 0
__krell_a64: .quad 0x7fffffffffffffff, 0
__krell_zero: .quad 0
__krell_2_63: .quad 0x43e0000000000000
__krell_2_64: .quad 0x43f0000000000000
.section .note.GNU-stack,"",@progbits
