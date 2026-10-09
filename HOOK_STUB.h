//=============================================================================
//  HOOK_STUB.h  --  BUILD-VERIFICATION STUBS.  NOT A WORKING HOOK.
//=============================================================================
//
//  WHY THIS FILE EXISTS
//  --------------------
//  rosINTERNALesp.cpp references two functions that exist in no library on
//  this machine and are defined nowhere in this repository:
//
//      DetourFunction(PBYTE, PBYTE)   -- rosINTERNALesp.cpp ~line 1045
//      DetourRemove (PBYTE, PBYTE)   -- rosINTERNALesp.cpp ~line 474
//
//  Neither is part of Microsoft Detours 4.0.1. Detours exposes DetourAttach,
//  DetourDetach and DetourTransactionBegin; it has no DetourFunction and no
//  DetourRemove. Because there is no declaration in scope at the call sites,
//  the compiler reports C3861 "identifier not found" -- a compile-stage
//  error, not a link-stage one.
//
//  To let the build AND the link step run to completion, and thereby verify
//  the whole toolchain (vendored DirectX SDK, vendored Detours, the v143 /
//  10.0.19041.0 retarget, and all four configurations), the two symbols are
//  declared and defined here.
//
//  WHAT THESE STUBS ACTUALLY DO
//  ----------------------------
//  Nothing at all.
//
//  DetourFunction returns its target address UNMODIFIED: no trampoline is
//  allocated, no prologue is disassembled, no 0xE9 jump is written, no bytes
//  are patched. DetourRemove is an empty function.
//
//  CONSEQUENCE -- READ THIS
//  -----------------------
//  The resulting rosINTERNALesp.dll WILL BUILD AND WILL LOAD. It will NOT
//  hook the D3D9 vtable. The ESP overlay, chams and aimbot paths inside
//  rosINTERNALesp.cpp will never execute. This is a build-verification
//  artifact only. It is not a functional release build.
//
//  The prologue-patching and trampoline construction this project implements
//  elsewhere already lives in CTools::DetourCreate (CTools.cpp:131); the
//  two functions above are deliberately NOT reproduced here.
//=============================================================================
#ifndef ROSINTERNALESP_HOOK_STUB_H
#define ROSINTERNALESP_HOOK_STUB_H

// PBYTE is declared by <Windows.h>, which rosINTERNALesp.cpp includes
// ahead of this header.

// Build-verification stub. Returns the target UNCHANGED; installs no hook.
inline void *DetourFunction(unsigned char *pTarget, unsigned char *pHook)
{
    (void)pHook;
    return (void *)pTarget;
}

// Build-verification stub. No-op; there is no installed hook to remove.
inline void DetourRemove(unsigned char *pTarget, unsigned char *pHook)
{
    (void)pTarget;
    (void)pHook;
}

#endif // ROSINTERNALESP_HOOK_STUB_H