# Licensed under the Solderpad Hardware Licence, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# SPDX-License-Identifier: Apache-2.0 WITH SHL-2.0
# You may obtain a copy of the License at https://solderpad.org/licenses/
#
# Original Author: Alessandro Mandrile (alessandro.mandrile99@gmail.com)

#*****************************************************************************
# interrupt_autosave.S
#-----------------------------------------------------------------------------
#

  .globl main
main:
# core of the test
  la t1, exception_handler
  csrw mtvec, t1  ## Load the address of the exception handler into MTVEC
  csrw 0x341, zero  ## Writing Zero to MEPC CSR
  csrw 0x342, zero  ## Writing Zero to MCAUSE CSR
  #End Handle exceptions

# enable software interrupts
  li a1, 0x8
  csrw mie, a1
#set software interrupt as pending
  #li a1, 0x8
  #csrs mip, a1
#load registers
#preserve return address
  li x1, 1     // ra
#let's not touch sp
  #li x2, 2
  #li x3, 3
  #li x4, 4
  li x5, 5     // t0
  li x6, 6     // t1
  li x7, 7     // t2
  #li x8, 8
  #li x9, 9
  li x10, 10   // a0
  li x11, 11   // a1
  li x12, 12   // a2
  li x13, 13   // a3
  li x14, 14   // a4
  li x15, 15   // a5
  li x16, 16   // a6
  li x17, 17   // a7
  #li x18, 18
  #li x19, 19
  #li x20, 20
  #li x21, 21
  #li x22, 22
  #li x23, 23
  #li x24, 24
  #li x25, 25
  #li x26, 26
  #li x27, 27
  li x28, 28   // t3
  li x29, 29   // t4
  li x30, 30   // t5
  li x31, 31   // t6

  ecall
#enable global interrupt
  li t0, 0x8
  csrw mstatus, t0
#should be useless
  #csrr a2, mstatus

jump00:
  j jump00


test_done:
    li a0, 0
    slli a0, a0, 1
    addi a0, a0, 1
    sw a0, tohost, t5
    self_loop: j self_loop

pass:
  li a0, 0
  j exit

fail:
  li a0, 1
  j exit

.align 8
exception_handler:
    # increment return address to skip instruction generating the exception
    # valid only if faulting instruction is not compressed (4-byte long)
  #push t0
    addi sp, sp, -16
    sd  s0, 0(sp)
    sd  s1, 8(sp)
    ld s0, 16+0(sp) //ra
    li s1, 1
    bne s0, s1, ld_fail
  #write pass to mepc
    la  s0, pass
    j continue
ld_fail:
  #write fail to mepc
    la  s0, fail
continue:
    csrw 0x341, s0
  #clear interrupt
    li s0, 0x8
    csrc mip, s0
  #pop
    ld s0, 0(sp)
    addi sp, sp, 8
    mret
