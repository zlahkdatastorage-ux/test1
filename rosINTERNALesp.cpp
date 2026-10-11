// rosINTERNALesp.cpp : Defines the entry point for the console application.
//

#include "stdafx.h"
#include "Windows.h"
#include "intrin.h"
#include "d3d9.h"
#include <iostream>
#include "d3dx9.h"
#include <vector>
#include "Colors.h"
#pragma comment(lib, "d3d9.lib")
#pragma comment(lib, "d3dx9.lib")
#include <assert.h>
#include <cstdint>
#include <type_traits>
#include <fstream>      // std::ofstream
#include <thread>
#include "CMenu.h"
#include "CSound.h"
#include <detours.h>
#pragma comment(lib, "detours.lib")
#include <psapi.h>
#pragma comment(lib, "psapi.lib")

using namespace std;

// Missing declarations (were in a different version's draw.h)
static ID3DXFont* font = NULL;
static bool xdxd = true;
static UINT mStartregister = 0;
static UINT mVectorCount = 0;

void drawesp(IDirect3DDevice9* pDevice);

// ---------------------------------------------------------
// RUNTIME OFFSETS (Populated by PatternScanner)
// ---------------------------------------------------------
uintptr_t OFFSET_CLIENT = 0;
uintptr_t OFFSET_RENDERER = 0;
uintptr_t OFFSET_VIEWMATRIX = 0;
uintptr_t OFFSET_LOCALPLAYER = 0;
uintptr_t OFFSET_PYGAME = 0;

#define LANG_HUMAN "Human"
#define LANG_ROBOT "Robot"
#define LANG_VEHICLE  "Vehicle"
#define LANG_ITEM  "Item"
#define LANG_SUPPLY  "Supply"
#define LANG_PLANE  "Plane"
#define LANG_WEAPON  "Weapon"

bool Player, Bot, Vehicle, Item, SuplyBox, Plane, weapon;
static bool wallhacks = true;
static int color = 1;
static bool multi = true;
static bool lines = false;

static bool ingame = true;

static bool esp = true;
static bool menu = true;

UINT Stride;
bool InitOnce = true;

D3DVIEWPORT9 Viewport;
static HMODULE Hand;
static DWORD id;
static HANDLE processHandle;

// CRITICAL 64-BIT FIX: DWORD is 32-bit, uintptr_t is 64-bit.
static uintptr_t BAddress; 
DWORD addPrim;

typedef HRESULT(APIENTRY *Present)(LPDIRECT3DDEVICE9, CONST RECT*, CONST RECT*, HWND, CONST RGNDATA*); //17
HRESULT APIENTRY Present_hook(LPDIRECT3DDEVICE9, CONST RECT*, CONST RECT*, HWND, CONST RGNDATA*);
Present Present_orig = 0;

typedef HRESULT(APIENTRY *SetStreamSource_t)(IDirect3DDevice9*, UINT, IDirect3DVertexBuffer9*, UINT, UINT);
HRESULT APIENTRY SetStreamSource_hook(IDirect3DDevice9*, UINT, IDirect3DVertexBuffer9*, UINT, UINT);
SetStreamSource_t SetStreamSource_orig = 0;

typedef HRESULT(APIENTRY *SetVertexShaderConstantF_t)(IDirect3DDevice9*, UINT, const float*, UINT);
HRESULT APIENTRY SetVertexShaderConstantF_hook(IDirect3DDevice9*, UINT, const float*, UINT);
SetVertexShaderConstantF_t SetVertexShaderConstantF_orig = 0;

typedef HRESULT(APIENTRY *SetTexture_t)(IDirect3DDevice9*, DWORD, IDirect3DBaseTexture9 *);
HRESULT APIENTRY SetTexture_hook(IDirect3DDevice9*, DWORD, IDirect3DBaseTexture9 *);
SetTexture_t SetTexture_orig = 0;

typedef HRESULT(APIENTRY *SetTransform_t)(IDirect3DDevice9*, D3DTRANSFORMSTATETYPE, const D3DXMATRIX*);
HRESULT APIENTRY SetTransform_hook(IDirect3DDevice9*, D3DTRANSFORMSTATETYPE, const D3DXMATRIX*);
SetTransform_t SetTransform_orig = 0;

typedef HRESULT(APIENTRY *Reset_t)(IDirect3DDevice9*, D3DPRESENT_PARAMETERS*);
HRESULT APIENTRY Reset_hook(IDirect3DDevice9*, D3DPRESENT_PARAMETERS*);
Reset_t Reset_orig = 0;

typedef HRESULT(APIENTRY *DrawIndexedPrimitive_t)(LPDIRECT3DDEVICE9, D3DPRIMITIVETYPE, INT, UINT, UINT, UINT, UINT);
HRESULT APIENTRY DrawIndexedPrimitive_hook(LPDIRECT3DDEVICE9, D3DPRIMITIVETYPE, INT, UINT, UINT, UINT, UINT);
DrawIndexedPrimitive_t DrawIndexedPrimitive_orig = 0;

// Detours 4.x hook state flags - track which hooks were successfully attached
static bool g_PresentHooked = false;
static bool g_SetStreamSourceHooked = false;
static bool g_SetVertexShaderConstantFHooked = false;
static bool g_SetTextureHooked = false;
static bool g_ResetHooked = false;
static bool g_SetTransformHooked = false;
static bool g_DrawIndexedPrimitiveHooked = false;
// Overlay state block (black-screen fix): snapshot ALL device state before
// our overlay draws, Apply before Present_orig - our PS=NULL/FVF/blend
// changes must never leak into the game's next frame.
static IDirect3DStateBlock9* g_OverlayStateBlock = NULL;
// Original render target to restore after overlay draws (state blocks do NOT
// capture RTs). NULL unless we had to redirect a non-backbuffer RT to draw.
static IDirect3DSurface9* g_prevOverlayRT = NULL;

// D3D9 pipeline matrix capture: drawesp prefers View*Proj captured from
// SetTransform over the (broken in x64) world->scene->camera memory chain.
static D3DXMATRIX g_capturedView;
static D3DXMATRIX g_capturedProj;
static bool g_hasCapturedView = false;
static bool g_hasCapturedProj = false;
// Per-register "changed at least once since inject" bits for the mirrored
// shader constant file. Camera/view matrices move with the player; UI
// transforms stay frozen - drawesp uses this to pick the right group.
static unsigned char g_dynReg[256];

// ---- draw-time ESP (Ros-D3D technique adapted to this build) -------------
// This build uploads one 4x4 world matrix per drawn entity at c4 or c12
// (discover.h: "SetVertexShaderConstantF r4/r12 x4 = one upload per drawn
// entity"); VP lives at c0-c3. Ros-D3D proves the technique on this game
// family: project the model origin at DRAW time instead of walking the
// entity list (whose legacy offsets we proved dead: world+0x278 is a
// UTF-16 string in this build).
static float    g_world4[16] = { 0 };
static float    g_world12[16] = { 0 };
static bool     g_hasWorld4 = false, g_hasWorld12 = false;
// c0/c4 upload streams (SVSCF-probed this session): c0 with n==4 = CAMERA
// VP (projection diag + row4 -623..|622); c4 with n==4 = per-entity WORLD
// matrix (rotation + row4 translation, w=1), one per drawn entity, roughly
// pool-index order per validate.txt ("r4=54 pool=55 -> MAPPED"). Present
// snapshots both at ENTRY (before menu/ESP draw calls pollute them) and
// resets the accumulators. ESP positions pair pool[i] with the r4 frame
// buffer; the VP comes from the STRICT c0 n==4 stream.
static float    g_wmSeqA[1024][16];
static float    g_wmFrame[1024][16];
static unsigned g_wmSeqN = 0;      // accumulating during the game's draws
static unsigned g_wmFrameN = 0;    // snapshot consumed by this frame's drawesp
// chams freshness window: the DIP hook may only cham within a few draws of
// an actual r4 entity upload (stale hit used to keep world geometry chammed
// for whole frames while seqN stayed constant).
static unsigned g_dipsSinceR4 = 0;
static ULONGLONG g_r4TickMs = 0;
// c0 stream: the alternative per-entity WVP candidate (r4 turned out to be
// shared in some sessions - distinct-row4 counting tells which stream holds
// ONE MATRIX PER ENTITY; Present auto-selects stream + origin convention).
static float    g_vpSeqA[1024][16];
static float    g_vpFrame[1024][16];
static unsigned g_vpSeqN = 0;
static unsigned g_vpFrameN = 0;
static int      g_lastDist4 = 0, g_lastDist0 = 0;  // distinct row4 (last frame)
static int      g_entStream = -1;   // -1 not yet selected, 0 = c4, 1 = c0
static int      g_entColMode = 0;   // 0 = row4 origin (row-vector), 1 = col4
static unsigned g_r4junk = 0;              // non-affine c4 uploads (rejected)
static int      g_poolN = 0;               // last STABLE pool count (telemetry)
// draw-order recorder: DIP-resolved (streamIdx:poolName) sequence per
// frame - the pairing ground truth logged by Present ("drawseq:").
static char     g_drawSeq[700];
static unsigned g_drawSeqN = 0;
static int      g_lastRecIdx = -1;
static char     g_lastDrawNm[24] = "?";
// stream-0 vertex buffer bound around each upload -> per-DIP verification
// (the DIP must draw the VB we saw uploaded; mismatch = idx-map pointing
// at the wrong draw). Also a live measure of the pool<->upload pairing.
static IDirect3DVertexBuffer9* g_wmVB[1024] = { 0 };
static IDirect3DVertexBuffer9* g_lastVB0 = NULL;
static unsigned g_vbOk = 0, g_vbMis = 0;
// draw-time entity map: at each fresh DIP the CURRENT draw resolves to
// pool[idx] (the same map chams uses - visually validated in-game). We
// mark that entry DRAWN and pin its matrix (the upload that opened the
// freshness window). drawesp pairs pool[i] with ITS OWN drawn matrix
// instead of the i-th stream slot - upload order != pool order was
// proven by idx0 flapping between 56 m and 743 m depth. Entities never
// drawn (culled/far) get no box - correct ESP behavior.
static unsigned g_rigSkip = 0;   // consecutive-duplicate collapses (session)
static float    g_drawPos[4096][16];
static unsigned char g_drawnLive[4096];
static float    g_drawPosF[4096][16];
static unsigned char g_drawnF[4096];
static unsigned g_telW4 = 0, g_telW12 = 0;          // uploads (per 5s window)
static unsigned g_telHitW4 = 0, g_telHitW12 = 0;     // origin projected in-view
static unsigned g_telPushed = 0;                     // markers queued (window)
static UINT     g_telV[40];                          // vSize frequency table
static unsigned g_telVC[40];
static int      g_telVN = 0;
static unsigned g_telST = 0;                         // SetTexture calls (window)
static unsigned g_vsSeen = 0;                        // VS-bound probed (window)
static unsigned g_sss = 0;                           // SetStreamSource calls
static unsigned g_telDip = 0;                        // DrawIndexedPrimitive calls
static UINT     g_vpW = 0, g_vpH = 0;                // viewport cache (Present)
static unsigned g_wvpAttTotal = 0;                   // matrix-shaped probes (window)
// Multi-candidate WVP probe: this build's true combined world->clip matrix
// register is unknown in-match (c0 turned out to be world-scale, not VP),
// so project the model origin through EVERY register start - including
// UNALIGNED (c13 = the 2018/Ros-D3D WVP slot) - and count which one moves
// across the screen as the camera moves. Frozen UI matrices never move.
static unsigned g_wvpAtt[256];   // per start: matrix-shaped probes seen
static unsigned g_wvpMov[256];   // per start: in-viewport AND position moved
static float    g_wvpLx[256];    // last accepted screen pos (moved detect)
static float    g_wvpLy[256];
static unsigned g_winScore[256]; // PERSISTENT move score per source (never reset)
static int      g_winSrc = -1;   // sticky winner: only it draws boxes
struct TelMarker { float x, y; UINT vSize; int src; };  // src = SVS start reg
static std::vector<TelMarker> g_telMark;             // queued this frame
static void TelProject(LPDIRECT3DDEVICE9 pDevice);   // defined below SetTexture
static bool findnew(string str1, string str2);       // def below ClientApp (DIP chams gate)
static bool IsPlayerName(const string& nm);          // shared player-only classifier (ESP + chams)
// Cached VP from the 2018 memory chain (ini/camera+0xC4), refreshed at most
// every 100ms - lets the probe compose world(c4/c12) x VP = W2S directly.
static float    g_memVP[16] = { 0 };
static bool     g_hasMemVP = false;

// Mirror of the vertex shader constant file (c0..c255) + bounded log counters
// for the SetVertexShaderConstantF diagnostics (max 40 lines ever).
static float g_vsConst[256][4];
static bool g_vsConstInit = false;
static int g_svsTotal = 0;
static int g_svsPlain = 0;
static int g_svsMatrix = 0;

LPDIRECT3DTEXTURE9 Red, Green, Blue, Yellow, Orange, Purple;

struct Vector3
{
	float x;
	float y;
	float z;
};

void log(string text, bool newline = true)
{
	if (false)
	{
		std::ofstream outfile;
		outfile.open("rosINTERNALesp_log.txt", std::ios_base::app);
		if (newline)
			outfile << text.c_str() << endl;
		else
			outfile << text.c_str();
	}
}

// One-time diagnostics that ALWAYS write to the log file. Used for offset
// resolution / hook status / first Present. Never call this per frame.
static void logInit(const string& text)
{
	// ALWAYS write %TEMP% first so the log is findable regardless of the
	// game's CWD (ros64's CWD is neither the game dir nor writable in some
	// launches - the old build then produced NO log at all, which looked
	// exactly like "injection did nothing").
	char tmp[300];
	bool wroteTemp = false;
	if (GetTempPathA(300, tmp) > 0)
	{
		std::ofstream t;
		t.open((string(tmp) + "rosINTERNALesp_log.txt").c_str(), std::ios_base::app);
		if (t.is_open())
		{
			t << text.c_str() << endl;
			wroteTemp = true;
		}
	}
	// Also keep the historical CWD copy - unless the CWD *is* %TEMP% (ros64
	// launched via Mirae Labs Launcher), which used to append every line
	// twice to the same file and made one-time logs look like repeated
	// init cycles.
	char cwdPath[MAX_PATH] = { 0 };
	if (GetCurrentDirectoryA(MAX_PATH, cwdPath) > 0)
	{
		char fullTemp[MAX_PATH] = { 0 }, cwdFile[MAX_PATH] = { 0 }, fullCwd[MAX_PATH] = { 0 };
		GetFullPathNameA(tmp, MAX_PATH, fullTemp, NULL);
		sprintf_s(cwdFile, "%s\\rosINTERNALesp_log.txt", cwdPath);
		GetFullPathNameA(cwdFile, MAX_PATH, fullCwd, NULL);
		if (wroteTemp && _stricmp(fullTemp, fullCwd) == 0)
			return;
	}
	std::ofstream outfile;
	outfile.open("rosINTERNALesp_log.txt", std::ios_base::app);
	if (outfile.is_open())
		outfile << text.c_str() << endl;
}

// ---------------------------------------------------------
// PATTERN SCANNER
// ---------------------------------------------------------
class PatternScanner {
public:
    static uintptr_t GetModuleBase() {
        return (uintptr_t)GetModuleHandle(NULL);
    }

    static MODULEINFO GetModuleInfo() {
        MODULEINFO modInfo = { 0 };
        HMODULE hModule = GetModuleHandle(NULL);
        if (hModule == 0) return modInfo;
        GetModuleInformation(GetCurrentProcess(), hModule, &modInfo, sizeof(MODULEINFO));
        return modInfo;
    }

    // Convert IDA-style pattern ("48 8B 05 ? ? ? ?") to byte array and mask
    static bool ParsePattern(const char* pattern, std::vector<int>& bytes, std::string& mask) {
        bytes.clear();
        mask.clear();
        const char* start = pattern;
        const char* end = pattern + strlen(pattern);
        for (const char* current = start; current < end; ++current) {
            if (*current == '?') {
                mask.push_back('?');
                bytes.push_back(0);
                current++;
                continue;
            }
            if (isxdigit((unsigned char)*current)) {
                char* endptr;
                long val = strtol(current, &endptr, 16);
                bytes.push_back((int)val);
                mask.push_back('x');
                current = endptr - 1;
            }
        }
        return !bytes.empty();
    }

    // Scan memory for the pattern
    static uintptr_t FindPattern(const char* pattern, uintptr_t start, size_t size) {
        std::vector<int> bytes;
        std::string mask;
        if (!ParsePattern(pattern, bytes, mask)) return 0;

        uintptr_t end = start + size - bytes.size();
        for (uintptr_t i = start; i < end; ++i) {
            bool found = true;
            for (size_t j = 0; j < bytes.size(); ++j) {
                if (mask[j] != '?' && *(unsigned char*)(i + j) != bytes[j]) {
                    found = false;
                    break;
                }
            }
            if (found) return i;
        }
        return 0;
    }

    // Resolve RIP-relative addresses (for instructions like mov rax, [rip+offset])
    static uintptr_t ResolveRelativeAddress(uintptr_t address, int offsetIndex, int instructionLength) {
        int32_t relativeOffset = *(int32_t*)(address + offsetIndex);
        return address + instructionLength + relativeOffset;
    }
};

// ---------------------------------------------------------
// OFFSET FILE (generated by locate_offsets.ps1)
// Format (hex RVAs, one per line, keys case-insensitive):
//   PYGAME=0x2DCA48
//   LOCALPLAYER=0x2EA28C
//   RENDERER=0x0
// ---------------------------------------------------------
static bool LoadOffsetsFromIni()
{
	// Search order: CWD (historical), next to ros64.exe, %TEMP% (ros64's CWD
	// when launched via Mirae Labs Launcher - the old log landed there), and
	// next to this DLL. Every attempt + the winning path get logged, because
	// a silent CWD miss used to leave OFFSET_* at 0 with no clue why.
	char cand[4][400];
	int n = 0;
	sprintf_s(cand[n++], 400, "rosINTERNALesp_offsets.ini");

	char exePath[400] = { 0 };
	if (GetModuleFileNameA(NULL, exePath, 400))
	{
		char* sl = strrchr(exePath, '\\');
		if (sl) { *sl = '\0'; sprintf_s(cand[n++], 400, "%s\\rosINTERNALesp_offsets.ini", exePath); }
	}
	char tmpPath[300] = { 0 };
	if (GetTempPathA(300, tmpPath) > 0)
		sprintf_s(cand[n++], 400, "%srosINTERNALesp_offsets.ini", tmpPath);

	HMODULE self = NULL;
	if (GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
		(LPCSTR)&LoadOffsetsFromIni, &self) && self)
	{
		char dllPath[400] = { 0 };
		if (GetModuleFileNameA(self, dllPath, 400))
		{
			char* sl = strrchr(dllPath, '\\');
			if (sl) { *sl = '\0'; sprintf_s(cand[n++], 400, "%s\\rosINTERNALesp_offsets.ini", dllPath); }
		}
	}

	char line[256];
	char key[64];
	unsigned long long val = 0;
	const char* used = NULL;

	for (int i = 0; i < n && !used; i++)
	{
		std::ifstream ini(cand[i]);
		if (!ini.is_open())
			continue;

		bool found = false;
		while (ini.getline(line, sizeof(line)))
		{
			if (line[0] == ';' || line[0] == '#' || line[0] == '\0')
				continue;
			if (sscanf_s(line, "%63[^=]=%llx", key, (unsigned)sizeof(key), &val) != 2)
				continue;

			if (_stricmp(key, "PYGAME") == 0)      { OFFSET_PYGAME = (uintptr_t)val;      found = true; }
			if (_stricmp(key, "LOCALPLAYER") == 0) { OFFSET_LOCALPLAYER = (uintptr_t)val; found = true; }
			if (_stricmp(key, "VIEWMATRIX") == 0)  { OFFSET_VIEWMATRIX = (uintptr_t)val;  found = true; }
			if (_stricmp(key, "RENDERER") == 0)    { OFFSET_RENDERER = (uintptr_t)val;    found = true; }
		}
		if (found)
			used = cand[i];
	}

	if (!used)
	{
		char buf[560];
		sprintf_s(buf, sizeof(buf),
			"INI MISSING: rosINTERNALesp_offsets.ini not found in any of %d paths (CWD/exe/TEMP/dll). OFFSET_* stay 0 - ESP disabled until the ini is placed there.",
			n);
		logInit(buf);
		return false;
	}

	char buf[400];
	sprintf_s(buf, sizeof(buf), "Offsets loaded from '%s' => PyGame:0x%llX LocalPlayer:0x%llX Renderer:0x%llX",
		used, (unsigned long long)OFFSET_PYGAME, (unsigned long long)OFFSET_LOCALPLAYER, (unsigned long long)OFFSET_RENDERER);
	logInit(buf);
	return true;
}

// ---------------------------------------------------------
// INITIALIZE OFFSETS (Runs at startup)
// ---------------------------------------------------------
void InitializeOffsets() {
    MODULEINFO modInfo = PatternScanner::GetModuleInfo();
    uintptr_t base = (uintptr_t)modInfo.lpBaseOfDll;

    // Prefer explicit offsets from rosINTERNALesp_offsets.ini (written by
    // locate_offsets.ps1 or the analysis sessions). The pattern scan below
    // stays as a last resort until real signatures are filled in.
    if (LoadOffsetsFromIni() && OFFSET_PYGAME != 0)
    {
        // Hard-validate the world-pointer slot: *(base + PYGAME + 0x410).
        // Range check rejects 0, non-canonical userspace, and the classic
        // 0xFFFFFFFF00000000 garbage produced by a stale/wrong ini value.
        // On failure PYGAME is zeroed so drawesp logs the explicit
        // "OFFSET_PYGAME is 0" error instead of reading junk.
        unsigned long long world = 0;
        ReadProcessMemory(GetCurrentProcess(), (LPCVOID)(base + OFFSET_PYGAME + 0x410), &world, sizeof(world), NULL);
        bool ok = world > 0x10000 && world < 0x0000800000000000ULL && (world >> 32) != 0xFFFFFFFF;
        char vbuf[220];
        // Do NOT zero OFFSET_PYGAME when the slot is empty. This runs on the
        // very first Present, while the game is still on its own menu /
        // loading screens and the world object legitimately does not exist
        // yet - the old "if (!ok) OFFSET_PYGAME = 0" then disabled ESP
        // permanently ("OFFSET_PYGAME is 0 - ESP disabled"). ResolveWorld
        // retries the same slot every frame and only caches a layout mode
        // once a pointer actually validates, so an empty slot at boot is
        // harmless and self-heals once a match starts.
        sprintf_s(vbuf, sizeof(vbuf), "PYGAME slot *(base+0x%llX+0x410) = 0x%llX => %s",
            (unsigned long long)OFFSET_PYGAME, world,
            ok ? "OK" : "empty/invalid at init - deferring (world not created yet, retry per frame)");
        logInit(vbuf);
        return;
    }

    logInit("ini load FAILED (no keys) - falling back to placeholder pattern scan (unreliable).");
    size_t size = modInfo.SizeOfImage;

    // TODO: REPLACE THESE PLACEHOLDER SIGNATURES WITH REAL ONES FROM x64dbg
    // Every signature must point at a DIFFERENT global pointer, otherwise the
    // scan returns the same address for all four offsets. The assignments below
    // are WIRED UP now: while they were commented out, OFFSET_* stayed 0 and
    // the ESP read from module base + 0x410 etc. (i.e. nothing ever rendered
    // no matter how "correct" the offsets were).
    char buf[160];

    // 1. PyGame
    uintptr_t pyGamePtr = PatternScanner::FindPattern("48 8B 05 ? ? ? ? 48 8B 88 ? ? ? ? 48 85 C9", base, size);
    if (pyGamePtr) {
        OFFSET_PYGAME = PatternScanner::ResolveRelativeAddress(pyGamePtr, 3, 7) - base;
        sprintf_s(buf, sizeof(buf), "Found PyGame offset: 0x%llX", (unsigned long long)OFFSET_PYGAME);
        logInit(buf);
    } else {
        logInit("Failed to find PyGame pattern!");
    }

    // 2. LocalPlayer
    uintptr_t localPlayerPtr = PatternScanner::FindPattern("48 8B 05 ? ? ? ? 48 8B 88 ? ? ? ? 48 85 C9", base, size); // Replace with real sig
    if (localPlayerPtr) {
        OFFSET_LOCALPLAYER = PatternScanner::ResolveRelativeAddress(localPlayerPtr, 3, 7) - base;
        sprintf_s(buf, sizeof(buf), "Found LocalPlayer offset: 0x%llX", (unsigned long long)OFFSET_LOCALPLAYER);
        logInit(buf);
    } else {
        logInit("Failed to find LocalPlayer pattern!");
    }

    // 3. ViewMatrix
    uintptr_t viewMatrixPtr = PatternScanner::FindPattern("48 8B 05 ? ? ? ? 48 8D 0D ? ? ? ?", base, size); // Replace with real sig
    if (viewMatrixPtr) {
        OFFSET_VIEWMATRIX = PatternScanner::ResolveRelativeAddress(viewMatrixPtr, 3, 7) - base;
        sprintf_s(buf, sizeof(buf), "Found ViewMatrix offset: 0x%llX", (unsigned long long)OFFSET_VIEWMATRIX);
        logInit(buf);
    } else {
        logInit("Failed to find ViewMatrix pattern!");
    }

    // 4. Renderer
    uintptr_t rendererPtr = PatternScanner::FindPattern("48 8B 05 ? ? ? ? 48 8B 88 ? ? ? ? 48 85 C9", base, size); // Replace with real sig
    if (rendererPtr) {
        OFFSET_RENDERER = PatternScanner::ResolveRelativeAddress(rendererPtr, 3, 7) - base;
        sprintf_s(buf, sizeof(buf), "Found Renderer offset: 0x%llX", (unsigned long long)OFFSET_RENDERER);
        logInit(buf);
    } else {
        logInit("Failed to find Renderer pattern!");
    }

    sprintf_s(buf, sizeof(buf), "Offsets => PyGame:0x%llX LocalPlayer:0x%llX ViewMatrix:0x%llX Renderer:0x%llX",
        (unsigned long long)OFFSET_PYGAME, (unsigned long long)OFFSET_LOCALPLAYER,
        (unsigned long long)OFFSET_VIEWMATRIX, (unsigned long long)OFFSET_RENDERER);
    logInit(buf);
}

// ---------------------------------------------------------
// MEMORY CLASS
// ---------------------------------------------------------
class Memory
{
public:
	template <typename Type, typename Base, typename Offset>
	static inline Type Ptr(Base base, Offset offset)
	{
		static_assert(std::is_pointer<Type>::value || std::is_integral<Type>::value, "Type must be a pointer or address");
		static_assert(std::is_pointer<Base>::value || std::is_integral<Base>::value, "Base must be a pointer or address");
		static_assert(std::is_pointer<Offset>::value || std::is_integral<Offset>::value, "Offset must be a pointer or address");

		return base ? reinterpret_cast<Type>((reinterpret_cast<uint64_t>(base) + static_cast<uint64_t>(offset))) : nullptr;
	}

	template <typename Type>
	static bool IsValidPtr(Type* ptr)
	{
		return (ptr && sizeof(ptr)) ? true : false;
	}

	static bool IsValidPtr(void* ptr)
	{
		return (ptr && sizeof(ptr)) ? true : false;
	}
	template<typename T>
	static T ReadMemory(SIZE_T address)
	{
		T buffer{}; // zero-initialized: never return uninitialized stack data on failure
		if (!ReadProcessMemory(processHandle, (LPCVOID)address, &buffer, sizeof(T), NULL))
		{
			log("FAIL RPM");
		}
		return buffer;
	}

	template<typename T>
	static bool ReadMemoryC(SIZE_T address)
	{
		T buffer{};
		if (!ReadProcessMemory(processHandle, (LPCVOID)address, &buffer, sizeof(T), NULL))
		{
			return false;
		}
		return true;
	}

	static string ReadString(SIZE_T address, int Size)
	{
		// FIX: the old code passed &buffer (the std::string OBJECT) straight to
		// ReadProcessMemory. That overwrote the string header instead of its
		// character storage, so the string always came back empty and every
		// findnew() type check failed -> nothing was ever drawn. Read into a
		// plain char buffer and build the string from that instead.
		if (Size <= 0)
			return string();
		std::vector<char> buffer(Size + 1, '\0');
		SIZE_T bytesRead = 0;
		if (!ReadProcessMemory(processHandle, (LPCVOID)address, buffer.data(), Size, &bytesRead))
		{
			log("FAIL STR");
			return string();
		}
		buffer[Size] = '\0';
		return string(buffer.data());
	}
};

HRESULT APIENTRY SetStreamSource_hook(LPDIRECT3DDEVICE9 pDevice, UINT StreamNumber, IDirect3DVertexBuffer9* pStreamData, UINT OffsetInBytes, UINT sStride)
{
	g_sss++;   // audit: does the engine bind vertex streams per draw?
	if (StreamNumber == 0)
	{
		Stride = sStride;
		g_lastVB0 = pStreamData;   // VB binding snapshot for upload<->draw pairing
	}

	return SetStreamSource_orig(pDevice, StreamNumber, pStreamData, OffsetInBytes, sStride);
}

static bool ValOk(float v) { return v == v && v < 3.0e38f && v > -3.0e38f; }
static float AbsF(float v) { return v < 0 ? -v : v; }

// Heuristic: does this 4x4 group look like a transform matrix? Real matrices
// almost always contain at least one unit-ish value (rotation cos/sin, scale,
// or the implicit 1 on the w row/column).
static bool LooksLikeMatrix(const float* m16)
{
	for (int i = 0; i < 16; i++)
	{
		if (!ValOk(m16[i]))
			return false;
		float a = AbsF(m16[i]);
		if (a >= 0.85f && a <= 1.15f)
			return true;
	}
	return false;
}

// strict capture gate: mirrors SeqAffinePos (drawesp). m[15]==1 plus a
// sane translation (>=2 components |t|>0.5, all <100000) in row4 OR col4.
// Non-affine c4 uploads (UI quads like "1.206/2.015/... m[15]=35.4",
// projection helpers) used to occupy stream slots and shift every
// pool[i]<->r4[i] pairing by their count - the box-teleport bug.
static bool R4SaneT(float x, float y, float z)
{
	if (x != x || y != y || z != z) return false;
	if (fabsf(x) > 100000.0f || fabsf(y) > 100000.0f || fabsf(z) > 100000.0f) return false;
	int nz = 0;
	if (fabsf(x) > 0.5f) nz++;
	if (fabsf(y) > 0.5f) nz++;
	if (fabsf(z) > 0.5f) nz++;
	return nz >= 2;
}
static bool R4AffineGate(const float* m)
{
	if (fabsf(m[15] - 1.0f) > 0.01f) return false;
	return R4SaneT(m[12], m[13], m[14]) || R4SaneT(m[3], m[7], m[11]);
}

HRESULT APIENTRY SetVertexShaderConstantF_hook(LPDIRECT3DDEVICE9 pDevice, UINT StartRegister, const float *pConstantData, UINT Vector4fCount)
{
	if (pConstantData != NULL)
	{
		mStartregister = StartRegister;
		mVectorCount = Vector4fCount;

		// Mirror the vertex constant file so drawesp can probe register groups.
		// While overwriting, flag registers whose value CHANGED - drawesp
		// prefers matrix groups that move (real camera) over frozen ones (UI).
		for (UINT i = 0; i < Vector4fCount && StartRegister + i < 256; i++)
		{
			float* dst = g_vsConst[StartRegister + i];
			const float* src = &pConstantData[i * 4];
			if (g_vsConstInit)
			{
				for (int k = 0; k < 4; k++)
					if (fabsf(dst[k] - src[k]) > 1e-4f) { g_dynReg[StartRegister + i] = 1; break; }
			}
			for (int k = 0; k < 4; k++)
				dst[k] = src[k];
		}
		g_vsConstInit = true;

		// --- capture per-draw world matrices even when an upload spans them.
		// Full-containment only, so a mixed block is never half-stale.
		if (StartRegister <= 4 && StartRegister + Vector4fCount >= 8)
		{
			memcpy(g_world4, pConstantData + (4 - StartRegister) * 4, sizeof(g_world4));
			g_hasWorld4 = true;
			g_telW4++;
		}
		if (StartRegister <= 12 && StartRegister + Vector4fCount >= 16)
		{
			memcpy(g_world12, pConstantData + (12 - StartRegister) * 4, sizeof(g_world12));
			g_hasWorld12 = true;
			g_telW12++;
		}
		// entity world matrix: STRICT n==4 only. The n==128 blocks at c4
		// are BONE PALETTES (identity/small translations, m[15]=1 on some)
		// - mixing them in made 69/72 frame entries fail the affine gate
		// and left only ARBITRARY pool indices paired with foreign matrices
		// ("vehicle text on floor items", "boxes freeze in place").
		// SVSCF "start=4 n=4 M D" is the real per-entity world matrix.
		if (StartRegister == 4 && Vector4fCount == 4)
		{
			// freshness opens on ANY r4 upload; the POSITION stream keeps
			// affine world matrices only, with CONSECUTIVE-DUPLICATE
			// COLLAPSE: one entity uploads its matrix once per pass
			// (body/shadow/depth -> 3-6x per frame), so identical
			// back-to-back translations = same entity -> refresh in
			// place, do NOT advance the stream index (else every pass
			// shifts every pool[i]<->slot mapping).
			g_dipsSinceR4 = 0;
			g_r4TickMs = GetTickCount64();
			if (R4AffineGate(pConstantData))
			{
				bool collapsed = false;
				if (g_wmSeqN > 0)
				{
					const float* lm = g_wmSeqA[g_wmSeqN - 1];
					const float* cm = pConstantData;
					float lx, ly, lz, cx, cy, cz;
					if (R4SaneT(lm[12], lm[13], lm[14])) { lx = lm[12]; ly = lm[13]; lz = lm[14]; }
					else                                 { lx = lm[3];  ly = lm[7];  lz = lm[11]; }
					if (R4SaneT(cm[12], cm[13], cm[14])) { cx = cm[12]; cy = cm[13]; cz = cm[14]; }
					else                                 { cx = cm[3];  cy = cm[7];  cz = cm[11]; }
					if (fabsf(cx - lx) < 0.2f && fabsf(cy - ly) < 0.2f &&
						fabsf(cz - lz) < 0.2f)
					{
						g_wmVB[g_wmSeqN - 1] = g_lastVB0;
						memcpy(g_wmSeqA[g_wmSeqN - 1], pConstantData, sizeof(g_wmSeqA[0]));
						g_rigSkip++;
						collapsed = true;
					}
				}
				if (!collapsed && g_wmSeqN < 1024)
				{
					g_wmVB[g_wmSeqN] = g_lastVB0;
					memcpy(g_wmSeqA[g_wmSeqN], pConstantData, sizeof(g_wmSeqA[0]));
					g_wmSeqN++;
				}
			}
			else
				g_r4junk++;
		}
		// c0 stream: the CAMERA VP. SVSCF diagnostics proved the upload
		// shape: "start=0 n=4 M D" carries the projection (diag .97/1.73/-1.02,
		// row4 -623,-623,615 | 622) while the n=128 blocks at c0 are OTHER
		// data (zeros/bone props). Capturing >=4 mixed them in, and the
		// latch then flapped between garbage entries every frame
		// ("VP: c0 stream[20]/[21]/[24]"). STRICT n==4 only.
		if (StartRegister == 0 && Vector4fCount == 4 && g_vpSeqN < 1024)
		{
			memcpy(g_vpSeqA[g_vpSeqN], pConstantData, sizeof(g_vpSeqA[0]));
			g_vpSeqN++;
		}

		// Bounded diagnostics: dump matrix-shaped register groups, but only the
		// first 2 samples PER start register, 20 per run total (the log
		// accumulated 600+ SVSCF lines across runs and drowned real events).
		if (Vector4fCount >= 4 && g_svsTotal < 20)
		{
			static int svsPerStart[64] = { 0 };   // slot = (start reg)/4, c0..c252
			UINT groups = Vector4fCount / 4;
			for (UINT g = 0; g < groups && g_svsTotal < 20; g++)
			{
				const float* m = pConstantData + g * 16;
				bool mlike = LooksLikeMatrix(m);
				if (!mlike && g_svsPlain >= 12)
					continue;
				int slot = ((int)StartRegister + (int)g * 4) / 4;
				if (slot < 0 || slot >= 64 || svsPerStart[slot] >= 2)
					continue;
				char buf[480];
				sprintf_s(buf, sizeof(buf),
					"SVSCF start=%u n=%u grp=%u%s%s: %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f",
					StartRegister + g * 4, Vector4fCount, g, mlike ? " M" : "",
					(g_dynReg[StartRegister + g * 4] ? " D" : ""),
					m[0], m[1], m[2], m[3], m[4], m[5], m[6], m[7],
					m[8], m[9], m[10], m[11], m[12], m[13], m[14], m[15]);
				logInit(buf);
				svsPerStart[slot]++;
				g_svsTotal++;
				if (mlike) g_svsMatrix++; else g_svsPlain++;
			}
		}
	}

	// draw-time probe RETIRED: drawesp now renders real entities from the
	// validated pool + r4 sequence (Stage 2). The probe burned ~2M matrix
	// tests/5s on the render thread and spammed marker boxes (FPS drop).
	// TelProject kept on disk for future discovery work.

	return SetVertexShaderConstantF_orig(pDevice, StartRegister, pConstantData, Vector4fCount);
}

// True iff the matrix equals the identity within 1e-3. The game pushes
// identity through SetTransform constantly; latching on that made drawesp
// "prefer" a matrix that transforms nothing (WorldToScreen became a no-op
// and nothing rendered).
static bool IsIdentityMatrix(const D3DXMATRIX& m)
{
	static const float id[16] = { 1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1 };
	const float* f = &m._11;
	for (int i = 0; i < 16; i++)
		if (fabsf(f[i] - id[i]) > 1e-3f)
			return false;
	return true;
}

// VP-shape invariant. THE OLD CHECKS WERE WRONG AND REJECTED EVERY REAL VP:
//   "_44 ~= 0"  -> for VP = V*P (row-vector, LH) element _44 = -dot(viewZ,eye)
//                  which is HUGE once the camera leaves the world origin.
//   "_34 ~= 1"  -> element _34 = viewZ.z which drops below 0.7 at pitch > 45.
// Consequence: the camera chain never latched; every run fell through to the
// garbage SVSCF c0 "VP" (log: "matrix source: SVSCF c0" only ever seen).
// Correct invariant: col4 of a LH perspective VP = (unit view-z-axis, -dot).
// Transposed (column-vector) storage puts that unit vector in row4 instead.
static bool IsVPShape(const D3DXMATRIX& m)
{
	const float* f = &m._11;
	for (int i = 0; i < 16; i++)
		if (f[i] != f[i] || fabsf(f[i]) > 1e7f)   // NaN/Inf/absurd
			return false;
	float nCol = sqrtf(f[3] * f[3] + f[7] * f[7] + f[11] * f[11]);
	float nRow = sqrtf(f[12] * f[12] + f[13] * f[13] + f[14] * f[14]);
	bool shape = (fabsf(nCol - 1.0f) <= 0.02f) || (fabsf(nRow - 1.0f) <= 0.02f);
	return shape && (f[0] != 0.0f || f[5] != 0.0f);
}

// ---- world -> screen through a latched VP -------------------------------
// Row-vector LH (D3DX):  clip = (x,y,z,1) * M
// Transposed storage:     clip = M * (x,y,z,1)
static bool g_vpColVec = false;      // layout selected by the idx0 test
static bool g_vpIdx0Checked = false; // idx0-on-screen proof done at least once
static D3DXMATRIX g_lastVP;          // last PROVEN VP (held across no-proof frames)
static bool g_lastVPCol = false;
static bool g_hasLastVP = false;

static bool ProjectThroughVP(const D3DXMATRIX& M, const D3DXVECTOR3& p,
	int W, int H, D3DXVECTOR3& out, float& wOut, bool colVec)
{
	const float* f = &M._11;
	float cx, cy, cw;
	if (!colVec)
	{
		cx = p.x * f[0] + p.y * f[4] + p.z * f[8] + f[12];
		cy = p.x * f[1] + p.y * f[5] + p.z * f[9] + f[13];
		cw = p.x * f[3] + p.y * f[7] + p.z * f[11] + f[15];
	}
	else
	{
		cx = p.x * f[0] + p.y * f[1] + p.z * f[2] + f[3];
		cy = p.x * f[4] + p.y * f[5] + p.z * f[6] + f[7];
		cw = p.x * f[12] + p.y * f[13] + p.z * f[14] + f[15];
	}
	if (cw <= 0.05f || cw > 100000.0f)
		return false;
	out.x = W * 0.5f * (cx / cw) + W * 0.5f;
	out.y = H * 0.5f - H * 0.5f * (cy / cw);
	wOut = cw;
	return true;
}

// The local player's world position MUST land inside the viewport through
// the real VP (the TPS camera keeps him on screen) - live proof that this
// candidate is actually the view-projection, not an arbitrary matrix.
// DEPTH SANITY (crash/flicker fix): the TPS camera rides 3-30m behind the
// local player, so a REAL VP gives idx0 depth in that ballpark (cap 1500m
// for plane/parachute/lobby cams). The broken selection used to accept
// candidates with idx0 depth 5000-9000m - those are shadow/UI passes whose
// "on screen" hit was a coincidence, and every other frame they flapped the
// boxes across the screen.
static bool Idx0PassesVP(const D3DXMATRIX& m, const D3DXVECTOR3& idx0,
	int W, int H, bool* pCol)
{
	D3DXVECTOR3 s; float w = 0;
	if (W <= 0 || H <= 0) return false;
	if (ProjectThroughVP(m, idx0, W, H, s, w, false) &&
		w >= 5.0f && w <= 5000.0f &&                 // 0.5m..500m depth sanity
		s.x >= 0.02f * W && s.x <= 0.98f * W &&
		s.y >= 0.05f * H && s.y <= 0.95f * H)
	{
		if (pCol) *pCol = false;
		return true;
	}
	if (ProjectThroughVP(m, idx0, W, H, s, w, true) &&
		w >= 5.0f && w <= 5000.0f &&                 // same sanity for col layout
		s.x >= 0.02f * W && s.x <= 0.98f * W &&
		s.y >= 0.05f * H && s.y <= 0.95f * H)
	{
		if (pCol) *pCol = true;
		return true;
	}
	return false;
}

// Shared acceptance gate for every candidate VP source: structural invariant
// + (at latch time) idx0-on-screen proof, which also picks the memory layout
// (row-vector vs transposed/column-vector).
static bool AcceptVP(const D3DXMATRIX& cand, D3DXMATRIX& out,
	bool haveIdx0, const D3DXVECTOR3& idx0)
{
	if (!IsVPShape(cand) || IsIdentityMatrix(cand))
		return false;
	if (!g_vpIdx0Checked && haveIdx0 && g_vpW > 0 && g_vpH > 0)
	{
		bool col = false;
		if (!Idx0PassesVP(cand, idx0, (int)g_vpW, (int)g_vpH, &col))
			return false;
		g_vpColVec = col;
		g_vpIdx0Checked = true;
		D3DXVECTOR3 s; float w = 0;
		ProjectThroughVP(cand, idx0, (int)g_vpW, (int)g_vpH, s, w, col);
		char b[170];
		sprintf_s(b, "VP latched: idx0->(%.0f,%.0f) depth=%.1fm layout=%s (idx0pos=%s)",
			s.x, s.y, w / 10.0f, col ? "col" : "row",
			haveIdx0 ? "mem/seq" : "unknown");
		logInit(b);
	}
	out = cand;
	return true;
}

// Captures the fixed-function VIEW / PROJECTION matrices straight from the
// device; drawesp prefers View*Proj from here over the memory chain.
// ONLY non-identity matrices are latched.
HRESULT APIENTRY SetTransform_hook(LPDIRECT3DDEVICE9 pDevice, D3DTRANSFORMSTATETYPE State, const D3DXMATRIX *pMatrix)
{
	if (pMatrix != NULL)
	{
		if (State == D3DTS_VIEW)
		{
			if (IsIdentityMatrix(*pMatrix))
			{
				static bool loggedIdV = false;
				if (!loggedIdV)
				{
					logInit("SetTransform VIEW = identity (ignored; no real view arrives via SetTransform)");
					loggedIdV = true;
				}
			}
			else
			{
				g_capturedView = *pMatrix;
				if (!g_hasCapturedView)
				{
					g_hasCapturedView = true;
					char buf[480];
					sprintf_s(buf, sizeof(buf),
						"SetTransform VIEW captured: %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f",
						g_capturedView._11, g_capturedView._12, g_capturedView._13, g_capturedView._14,
						g_capturedView._21, g_capturedView._22, g_capturedView._23, g_capturedView._24,
						g_capturedView._31, g_capturedView._32, g_capturedView._33, g_capturedView._34,
						g_capturedView._41, g_capturedView._42, g_capturedView._43, g_capturedView._44);
					logInit(buf);
				}
			}
		}
		else if (State == D3DTS_PROJECTION)
		{
			if (IsIdentityMatrix(*pMatrix))
			{
				static bool loggedIdP = false;
				if (!loggedIdP)
				{
					logInit("SetTransform PROJECTION = identity (ignored; no real proj arrives via SetTransform)");
					loggedIdP = true;
				}
			}
			else
			{
				g_capturedProj = *pMatrix;
				if (!g_hasCapturedProj)
				{
					g_hasCapturedProj = true;
					char buf[480];
					sprintf_s(buf, sizeof(buf),
						"SetTransform PROJECTION captured: %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f | %.3f %.3f %.3f %.3f",
						g_capturedProj._11, g_capturedProj._12, g_capturedProj._13, g_capturedProj._14,
						g_capturedProj._21, g_capturedProj._22, g_capturedProj._23, g_capturedProj._24,
						g_capturedProj._31, g_capturedProj._32, g_capturedProj._33, g_capturedProj._34,
						g_capturedProj._41, g_capturedProj._42, g_capturedProj._43, g_capturedProj._44);
					logInit(buf);
				}
			}
		}
	}

	return SetTransform_orig(pDevice, State, pMatrix);
}

HRESULT GenerateTexture(IDirect3DDevice9 *pDevice, IDirect3DTexture9 **ppD3Dtex, DWORD colour32)
{
	if (FAILED(pDevice->CreateTexture(8, 8, 1, 0, D3DFMT_A4R4G4B4, D3DPOOL_MANAGED, ppD3Dtex, NULL)))
		return E_FAIL;

	WORD colour16 = ((WORD)((colour32 >> 28) & 0xF) << 12)
		| (WORD)(((colour32 >> 20) & 0xF) << 8)
		| (WORD)(((colour32 >> 12) & 0xF) << 4)
		| (WORD)(((colour32 >> 4) & 0xF) << 0);

	D3DLOCKED_RECT d3dlr;
	(*ppD3Dtex)->LockRect(0, &d3dlr, 0, 0);
	WORD *pDst16 = (WORD*)d3dlr.pBits;

	for (int xy = 0; xy < 8 * 8; xy++)
		*pDst16++ = colour16;

	(*ppD3Dtex)->UnlockRect(0);

	return S_OK;
}

IDirect3DVertexShader9* vShader;

UINT vSize;
bool Direct3DInitialize = false;

IDirect3DPixelShader9 *Front, *Back;

// ---- refresh the cached memory VP (2018 chain / ini slot) ---------------
// Called from the probe at most every 100ms: 6 RPM reads, trivial cost.
static void UpdateMemVP()
{
	static ULONGLONG last = 0;
	ULONGLONG now = GetTickCount64();
	if (now - last < 100) return;
	last = now;

	// ini static VP first (fill via injector\vpscan.ps1 while in a match)
	if (OFFSET_VIEWMATRIX)
	{
		D3DXMATRIX m = Memory::ReadMemory<D3DXMATRIX>(BAddress + OFFSET_VIEWMATRIX);
		if (IsVPShape(m) && !IsIdentityMatrix(m))
		{
			memcpy(g_memVP, &m._11, sizeof(g_memVP));
			g_hasMemVP = true;
			return;
		}
	}
	// 2018-proven chain: world -> scene(+8) -> camera(+4/+8) -> VP +0xC4/0xC0/0xC8
	uintptr_t w = Memory::ReadMemory<uintptr_t>(BAddress + OFFSET_PYGAME + 0x410);
	if (w <= 0x10000) return;
	uintptr_t scene = Memory::ReadMemory<uintptr_t>(w + 0x8);
	if (scene <= 0x10000) return;
	uintptr_t cams[2] = { Memory::ReadMemory<uintptr_t>(scene + 4),
		Memory::ReadMemory<uintptr_t>(scene + 8) };
	const int offs[3] = { 0xC4, 0xC0, 0xC8 };
	for (int i = 0; i < 2; i++)
	{
		if (cams[i] < 0x10000 || cams[i] > 0x00007FFFFFFFFFFFULL) continue;
		for (int j = 0; j < 3; j++)
		{
			D3DXMATRIX m = Memory::ReadMemory<D3DXMATRIX>(cams[i] + offs[j]);
			if (IsVPShape(m) && !IsIdentityMatrix(m))
			{
				memcpy(g_memVP, &m._11, sizeof(g_memVP));
				g_hasMemVP = true;
				return;
			}
		}
	}
}

// ---- draw-time ESP v4: probe from SetVertexShaderConstantF ---------------
// Three projection sources per draw, all funnelled through one acceptor:
//   (a) every register start (incl. unaligned c13 = 2018/Ros-D3D WVP slot)
//   (b) per-entity world uploads (c4/c12) x VP from the 2018 memory chain
//       (camera+0xC4 or ini VIEWMATRIX) = correct W2S without entity lists
// Acceptor counts only in-viewport AND moving projections: a real camera
// WVP slides as you move, frozen UI matrices never do.
static void TelProject(LPDIRECT3DDEVICE9 pDevice)
{
	if (g_vpW == 0) return;

	// throttled shader-size probe (GetVertexShader works from any hook)
	static ULONGLONG lastVs = 0;
	ULONGLONG now = GetTickCount64();
	if (now - lastVs > 500)
	{
		lastVs = now;
		IDirect3DVertexShader9* vs = NULL;
		if (SUCCEEDED(pDevice->GetVertexShader(&vs)) && vs)
		{
			g_vsSeen++;
			UINT fs = 0;
			if (SUCCEEDED(vs->GetFunction(NULL, &fs)))
			{
				vSize = fs;
				int ti = -1;
				for (int i = 0; i < g_telVN; i++) if (g_telV[i] == vSize) { ti = i; break; }
				if (ti < 0 && g_telVN < 40) { ti = g_telVN++; g_telV[ti] = vSize; g_telVC[ti] = 0; }
				if (ti >= 0) g_telVC[ti]++;
			}
			vs->Release();
		}
	}

	UpdateMemVP();

	// Sticky winner selection: only ONE source draws boxes. Live data showed
	// c4 (per-entity matrices) dominating with ~8600 moves/5s while the UI
	// matrices bleeding through c0/c1/c3 produced the "random flying boxes".
	static ULONGLONG lastWin = 0;
	ULONGLONG nw = GetTickCount64();
	if (nw - lastWin > 500)
	{
		lastWin = nw;
		int best = -1; unsigned bv = 0;
		for (int g = 0; g < 256; g++)
			if (g_winScore[g] > bv) { bv = g_winScore[g]; best = g; }
		if (g_winSrc < 0)
		{
			if (best >= 0 && bv >= 60) g_winSrc = best;
		}
		else if (best >= 0 && best != g_winSrc && bv >= g_winScore[g_winSrc] * 3 + 200)
			g_winSrc = best;   // switch only on strong sustained evidence
	}

	const float W = (float)g_vpW, H = (float)g_vpH;
	auto accept = [&](int grp, const float* flat) -> void
	{
		float w = flat[15];                            // clip.w for origin
		if (w <= 0.1f || w > 100000.0f) return;
		float sx = W * 0.5f * (flat[12] / w) + W * 0.5f;   // row4.x / w
		float sy = H * 0.5f - H * 0.5f * (flat[13] / w);   // row4.y / w
		if (sx < 0.0f || sy < 0.0f || sx >= W || sy >= H) return;
		float dx = sx - g_wvpLx[grp], dy = sy - g_wvpLy[grp];
		bool first = (g_wvpLx[grp] == 0.0f && g_wvpLy[grp] == 0.0f);
		if (!first && dx * dx + dy * dy < 64.0f) return;   // <8 px: static
		g_wvpLx[grp] = sx; g_wvpLy[grp] = sy;
		g_wvpMov[grp]++;
		g_winScore[grp]++;
		if (grp != g_winSrc) return;   // boxes ONLY from the winning source
		bool dup = false;
		for (size_t d = 0; d < g_telMark.size() && !dup; d++)
			if ((int)(g_telMark[d].x / 16) == (int)(sx / 16) &&
				(int)(g_telMark[d].y / 16) == (int)(sy / 16)) dup = true;
		if (!dup && g_telMark.size() < 64)
		{
			g_telMark.push_back({ sx, sy, vSize, grp });
			g_telPushed++;
		}
	};

	// (a) every register start in the mirror
	if (g_vsConstInit)
	{
		for (int grp = 0; grp + 3 < 256; grp++)
		{
			float flat[16];
			for (int r = 0; r < 4; r++)
				for (int c = 0; c < 4; c++)
					flat[r * 4 + c] = g_vsConst[grp + r][c];
			if (!LooksLikeMatrix(flat))
				continue;
			g_wvpAttTotal++;
			g_wvpAtt[grp]++;
			accept(grp, flat);
		}
	}

	// (b) per-entity world (c4 / c12 upload) x VP from the 2018 memory chain
	if (g_hasMemVP && (g_hasWorld4 || g_hasWorld12))
	{
		for (int k = 0; k < 2; k++)
		{
			if (k == 0 && !g_hasWorld4) continue;
			if (k == 1 && !g_hasWorld12) continue;
			D3DXMATRIX world, vp, m;
			memcpy(world.m, k ? g_world12 : g_world4, sizeof(world.m));
			memcpy(vp.m, g_memVP, sizeof(vp.m));
			D3DXMatrixMultiply(&m, &world, &vp);       // row-vector: p * W * VP
			int src = k ? 212 : 200;
			g_wvpAttTotal++;
			g_wvpAtt[src]++;
			accept(src, (const float*)&m._11);
		}
	}
}

// ---- DrawIndexedPrimitive: THE per-draw entry point on this engine ------
// SetTexture never fires in-match (audit st=0) while DIP fires ~42k/5s and
// SetStreamSource ~49k/5s - so chams/wallhack/vSize now live HERE, before
// the original draw call (state set here is what the draw uses).
HRESULT APIENTRY DrawIndexedPrimitive_hook(LPDIRECT3DDEVICE9 pDevice, D3DPRIMITIVETYPE arg0, INT arg1, UINT arg2, UINT arg3, UINT arg4, UINT arg5)
{
	g_telDip++;
	g_dipsSinceR4++;   // per-DIP decay for the chams freshness window
	                   // (was never incremented - the "6 DIPs" never tightened)

	// textures were only generated in SetTexture (dead) - do it on first draw
	if (InitOnce)
	{
		InitOnce = false;
		GenerateTexture(pDevice, &Green, D3DCOLOR_RGBA(0, 255, 0, 255));
		GenerateTexture(pDevice, &Red, D3DCOLOR_ARGB(255, 255, 0, 0));
		GenerateTexture(pDevice, &Blue, D3DCOLOR_ARGB(255, 0, 0, 255));
		GenerateTexture(pDevice, &Yellow, D3DCOLOR_ARGB(255, 255, 255, 0));
		GenerateTexture(pDevice, &Orange, D3DCOLOR_ARGB(255, 255, 165, 0));
		GenerateTexture(pDevice, &Purple, D3DCOLOR_ARGB(255, 102, 0, 153));
	}

	// (vSize query removed: chams now identifies players via the entity-pool
	// name gate below, not via shader size - saves a GetVertexShader per draw)

	// ---- current draw's entity = pool entry mapped to this frame's r4
	// stream position (order-preserving map; begin/end cached once per
	// frame; name cached per stream position). Runs with chams OFF too:
	// the draw-order recorder below is the pairing ground truth, and
	// chams/ESP both consume the same map.
	{
		static uintptr_t c_pb = 0, c_pe = 0;
		static unsigned lastSeqSeen = 0xFFFFFFFF;
		if (g_wmSeqN < lastSeqSeen || c_pb == 0)
		{
			uintptr_t poolObj = BAddress + 0x2D30530;
			c_pb = Memory::ReadMemory<uintptr_t>(poolObj + 0x808);
			c_pe = Memory::ReadMemory<uintptr_t>(poolObj + 0x810);
		}
		lastSeqSeen = g_wmSeqN;

		static int cachedIdx = -1;
		static bool cachedHit = false;
		static unsigned cachedFrame = 0xFFFFFFFF;
		static char lastName[32] = "-";
		if (g_wmSeqN != cachedFrame) { cachedFrame = g_wmSeqN; cachedIdx = -1; }

		// tight freshness window: entity draw clusters come within a handful
		// of DIPs of their r4 upload. 6 DIPs/20ms still let world geometry
		// (doors/cars/trees) through - 3 DIPs/8ms keeps it player-only.
		bool fresh = (g_dipsSinceR4 <= 3) &&
			(GetTickCount64() - g_r4TickMs < 8);

		bool hit = false;
		if (g_wmSeqN >= 1 && c_pb > 0x10000 && c_pe > c_pb && (c_pe - c_pb) < 0x8000)
		{
			int pc = (int)((c_pe - c_pb) / 8);
			int idx = (int)g_wmSeqN - 1;
			// NEVER clamp: clamping made tail-end environment draws inherit
			// the LAST pool entry's name (a fence drawn after the uploads
			// resolved to pool[pc-1] and got chammed as that entity).
			if (idx >= 0 && idx < pc)
			{
				if (idx != cachedIdx)
				{
					cachedIdx = idx;
					cachedHit = false;
					uintptr_t e = Memory::ReadMemory<uintptr_t>(c_pb + (uintptr_t)idx * 8);
					if (e > 0x10000)
					{
						uintptr_t an = Memory::ReadMemory<uintptr_t>(e + 0x3B8);
						if (an > 0x10000)
						{
							string nm = Memory::ReadString(Memory::ReadMemory<uintptr_t>(an + 0x8), 24);
							// ONE shared classifier for chams AND ESP: loot,
							// wheels and static props (doors/blocks) live under
							// the same "character\..." namespace - see
							// IsPlayerName() for the full rejection list.
							cachedHit = IsPlayerName(nm);
							// draw-order recorder keeps EVERY resolved name
							// (players and props) for the drawseq beacon.
							sprintf_s(g_lastDrawNm, "%.23s", nm.c_str());
							// audit beacon: record ONLY names we will cham, so
							// "lastChammed" proves player-only (world-leak detect).
							if (cachedHit)
								sprintf_s(lastName, "%.31s", nm.c_str());
						}
					}
				}
				// VB verification (diagnostic): does this DIP draw the
				// stream-0 buffer bound around upload idx? High vbmis = the
				// upload<->draw pairing is wrong (evidence for the ESP fix).
				{
					IDirect3DVertexBuffer9* vb0 = NULL;
					UINT vbOff = 0, vbSt = 0;
					if (SUCCEEDED(pDevice->GetStreamSource(0, &vb0, &vbOff, &vbSt)) && vb0)
					{
						if (vb0 == g_wmVB[idx]) g_vbOk++; else g_vbMis++;
						vb0->Release();
					}
				}
				// draw-time entity map: this DIP's entity = pool[idx]
				// (chams-validated); pin ITS matrix (the upload that
				// opened the freshness window) - ESP consumes this map.
				if (idx < 4096)
				{
					g_drawnLive[idx] = 1;
					memcpy(g_drawPos[idx], g_wmSeqA[idx], sizeof(g_drawPos[0]));
				}
				hit = cachedHit && fresh;

				// draw-order recorder: (streamIdx:poolName) for each fresh
				// entity draw. Monotonic 0,1,2.. = pool order; gaps = pool
				// order minus culled; scrambled = pairing invalid. Logged by
				// Present every 5s ("drawseq:").
				if (fresh && idx != g_lastRecIdx)
				{
					g_lastRecIdx = idx;
					int o2 = (int)strlen(g_drawSeq);
					if (o2 < 600)
						sprintf_s(g_drawSeq + o2, sizeof(g_drawSeq) - o2,
							"%u:%.10s ", (unsigned)idx, g_lastDrawNm);
					g_drawSeqN++;
				}
			}
		}
		// chams telemetry: applied vs stale-blocked + vertex count of the
		// draws we cham (player-mesh signature for the next tuning pass)
		{
			static unsigned cApp = 0, cBlk = 0, cVerts = 0;
			static ULONGLONG cLog = 0;
			if (hit && opt.d3d.Chams) { cApp++; cVerts = arg3; }
			else if (cachedHit && opt.d3d.Chams) cBlk++;
			if (GetTickCount64() - cLog > 5000)
			{
				cLog = GetTickCount64();
				if (cApp + cBlk > 0 || g_vbOk + g_vbMis > 0)
				{
					char cb2[210];
					sprintf_s(cb2, "chams: applied=%u stale-blocked=%u vbok=%u vbmis=%u lastVerts=%u lastChammed=%.31s",
						cApp, cBlk, g_vbOk, g_vbMis, cVerts, lastName);
					logInit(cb2);
					cApp = cBlk = 0;
					g_vbOk = g_vbMis = 0;
				}
			}
		}
		if (hit && opt.d3d.Chams)
		{
			// c0 layout is (r,g,b,a) - proven by Ros-D3D's red constant
			// {1,0,0,1}. The old code passed {a,r,g,b} with a=0 unless the
			// "Alpha" box was ticked -> grey/black chams; "Red" was never
			// even read (option->component mapping was off by one).
			float r = 0.0f, g = 0.0f, b = 0.0f;
			if (opt.chamsopt.red)   r = 1.0f;
			if (opt.chamsopt.green) g = 1.0f;
			if (opt.chamsopt.blue)  b = 1.0f;
			if (!opt.chamsopt.red && !opt.chamsopt.green && !opt.chamsopt.blue)
				r = 1.0f;                          // default: red
			// Alpha option: OFF = opaque (proven look), ON = translucent
			// chams. (Was hardcoded 1.0 -> the toggle did nothing.)
			float a = opt.chamsopt.alpha ? 0.55f : 1.0f;
			float sColor[4] = { r, g, b, a };
			pDevice->SetPixelShaderConstantF(0, sColor, 4);

			float bias = 1000.0f;
			float bias_float = static_cast<float>(-bias);
			bias_float /= 10000.0f;
			pDevice->SetRenderState(D3DRS_DEPTHBIAS, *(DWORD*)&bias_float);
		}
		else if (opt.d3d.Chams)
		{
			pDevice->SetRenderState(D3DRS_DEPTHBIAS, 0);
		}
	}

	return DrawIndexedPrimitive_orig(pDevice, arg0, arg1, arg2, arg3, arg4, arg5);
}

HRESULT APIENTRY SetTexture_hook(LPDIRECT3DDEVICE9 pDevice, DWORD Sampler, IDirect3DBaseTexture9 *pTexture)
{
	g_telST++;   // telemetry: does this game ever reach SetTexture at all?
	if (InitOnce)
	{
		InitOnce = false;
		GenerateTexture(pDevice, &Green, D3DCOLOR_RGBA(0, 255, 0, 255));
		GenerateTexture(pDevice, &Red, D3DCOLOR_ARGB(255, 255, 0, 0));
		GenerateTexture(pDevice, &Blue, D3DCOLOR_ARGB(255, 0, 0, 255));
		GenerateTexture(pDevice, &Yellow, D3DCOLOR_ARGB(255, 255, 255, 0));
		GenerateTexture(pDevice, &Orange, D3DCOLOR_ARGB(255, 255, 165, 0));
		GenerateTexture(pDevice, &Purple, D3DCOLOR_ARGB(255, 102, 0, 153));
	}

	//get vSize (original per-draw refresh; telemetry/projection moved to the
	//SetVertexShaderConstantF hook - this engine is silent in SetTexture
	//in-match, audit st=0 with pure system3d9.dll)
	if (SUCCEEDED(pDevice->GetVertexShader(&vShader)))
		if (vShader != NULL)
		{
			if (SUCCEEDED(vShader->GetFunction(NULL, &vSize)))
				vShader->Release();
			vShader = NULL;
		}

	if (opt.d3d.Chams) {
		//wallhack
		pDevice->SetRenderState(D3DRS_DEPTHBIAS, 0);
		if (vSize == 2300 || vSize == 900 ||
			vSize == 1952 || vSize == 640 || Stride == 48 || vSize == 2300 || vSize == 900 ||
			vSize == 1952 || vSize == 640)//vSize == 1436
		{
			// color mapping parity with the DIP path: option N must drive
			// channel N (this block used to map green->r, blue->g, alpha->b
			// and passed {a,r,g,b} instead of {r,g,b,a}).
			float r = 0.0f, g = 0.0f, b = 0.0f;
			if (opt.chamsopt.red)   r = 1.0f;
			if (opt.chamsopt.green) g = 1.0f;
			if (opt.chamsopt.blue)  b = 1.0f;
			if (!opt.chamsopt.red && !opt.chamsopt.green && !opt.chamsopt.blue)
				r = 1.0f;                          // default: red
			float a = opt.chamsopt.alpha ? 0.55f : 1.0f;   // same as DIP path
			float sColor[4] = { r, g, b, a };
			pDevice->SetPixelShaderConstantF(0, sColor, 4);

			float bias = 1000.0f;
			float bias_float = static_cast<float>(-bias);
			bias_float /= 10000.0f;
			pDevice->SetRenderState(D3DRS_DEPTHBIAS, *(DWORD*)&bias_float);
		}
	}

	return SetTexture_orig(pDevice, Sampler, pTexture);
}

//nSeven
HRESULT DrawString(LPD3DXFONT Font, INT X, INT Y, DWORD dColor, CONST PCHAR cString, ...)
{
	HRESULT hRet;

	if (Font == NULL || cString == NULL)   // crash guard: draw before font init / bad ptr
		return E_FAIL;

	CHAR buf[512] = { NULL };
	va_list ArgumentList;
	va_start(ArgumentList, cString);
	_vsnprintf_s(buf, sizeof(buf), sizeof(buf) - strlen(buf), cString, ArgumentList);
	va_end(ArgumentList);

	RECT rc[2];
	SetRect(&rc[0], X, Y, X, 0);
	SetRect(&rc[1], X, Y, X + 50, 50);

	hRet = D3D_OK;

	if (SUCCEEDED(hRet))
	{
		Font->DrawTextA(NULL, buf, -1, &rc[0], DT_NOCLIP, 0xFF000000);
		hRet = Font->DrawTextA(NULL, buf, -1, &rc[1], DT_NOCLIP, dColor);
	}

	return hRet;
}

//lucastx
class ClientApp
{
public:
	static bool WorldToScreen(Vector3 pos, D3DXVECTOR3 &screen, D3DXMATRIX matrix, int windowWidth, int windowHeight)
	{
		D3DXVECTOR4 clipCoords;
		clipCoords.x = pos.x*matrix[0] + pos.y*matrix[4] + pos.z*matrix[8] + matrix[12];
		clipCoords.y = pos.x*matrix[1] + pos.y*matrix[5] + pos.z*matrix[9] + matrix[13];
		clipCoords.z = pos.x*matrix[2] + pos.y*matrix[6] + pos.z*matrix[10] + matrix[14];
		clipCoords.w = pos.x*matrix[3] + pos.y*matrix[7] + pos.z*matrix[11] + matrix[15];

		if (clipCoords.w < 0.1f)
			return false;

		D3DXVECTOR3 NDC;
		NDC.x = clipCoords.x / clipCoords.w;
		NDC.y = clipCoords.y / clipCoords.w;
		NDC.z = clipCoords.z / clipCoords.w;

		screen.x = (windowWidth / 2 * NDC.x) + (NDC.x + windowWidth / 2);
		screen.y = -(windowHeight / 2 * NDC.y) + (NDC.y + windowHeight / 2);
		return true;
	}
	static bool WorldToScreen(D3DXVECTOR3 pos, D3DXVECTOR3 &screen, D3DXMATRIX matrix, int windowWidth, int windowHeight)
	{
		D3DXVECTOR4 clipCoords;
		clipCoords.x = pos.x*matrix[0] + pos.y*matrix[4] + pos.z*matrix[8] + matrix[12];
		clipCoords.y = pos.x*matrix[1] + pos.y*matrix[5] + pos.z*matrix[9] + matrix[13];
		clipCoords.z = pos.x*matrix[2] + pos.y*matrix[6] + pos.z*matrix[10] + matrix[14];
		clipCoords.w = pos.x*matrix[3] + pos.y*matrix[7] + pos.z*matrix[11] + matrix[15];

		if (clipCoords.w < 0.1f)
			return false;

		D3DXVECTOR3 NDC;
		NDC.x = clipCoords.x / clipCoords.w;
		NDC.y = clipCoords.y / clipCoords.w;
		NDC.z = clipCoords.z / clipCoords.w;

		screen.x = (windowWidth / 2 * NDC.x) + (NDC.x + windowWidth / 2);
		screen.y = -(windowHeight / 2 * NDC.y) + (NDC.y + windowHeight / 2);
		return true;
	}
};

static int GetDistance(Vector3 v1, Vector3 v2, int Divide)
{
	D3DXVECTOR3 vector3;
	vector3.x = v1.x - v2.x;
	vector3.y = v1.y - v2.y;
	vector3.z = v1.z - v2.z;
	return (int)sqrt(pow((double)vector3.x, 2.0) + pow((double)vector3.y, 2.0) + pow((double)vector3.z, 2.0)) / Divide;
}

const char* getitemname(int a) {
	switch (a)
	{
	case 1: return "Lv 1 helmet";
	case 2: return "Lv 2 helmet";
	case 3:  return "Lv 3 helmet";
	case 5:  return "Lv 1 Armor";
	case 6:  return "Lv 2 Armor";
	case 7:  return "Lv 3 Armor";
	case 8:  return "Lv 1 Backpack";
	case 9:  return "Lv 2 Backpack";
	case 10:  return "Lv 3 Backpack";
	case 19:  return "Ghillie Suit";
	case 50:  return "Fuel Barrel";
	case 101:  return "Bandage";
	case 102:  return "Med Kit";
	case 103:  return "First Aid Kit";
	case 105:  return "Sports Drink";
	case 106:  return "Cardio Tonic";
	case 1001:  return "M4A1 Rifle";
	case 1002:  return "AKM Rifle";
	case 1003:  return "M870 SG";
	case 1004:  return "M1887 SG";
	case 1005:  return "AA12 SG";
	case 1006:  return "AWM SR";
	case 1007:  return "Barett SR";
	case 1008:  return "M249 MG";
	case 1009:  return "M14EBR Rifle";
	case 1010:  return "AR15 Rifle";
	case 1011:  return "MP7 SMG";
	case 1012:  return "PP19 SMG";
	case 1013:  return "Thompson SMG";
	case 1014:  return "G18C Pistol";
	case 1015:  return "Desert Eagle";
	case 1017:  return "Vector";
	case 1018:  return "P90 SMG";
	case 1019:  return "SAIGA-12 Shotgun";
	case 1020:  return "WRO Hunting Rifle";
	case 1021:  return "SVD SR";
	case 1022:  return "M110 Sniper Rifle";
	case 1023:  return "ACR Rifle";
	case 1024:  return "AN94 Rifle";
	case 1025:  return "MP5 SMG";
	case 1026:  return "AUG Rifle";
	case 1027:  return "QBU Sniper Rifle";
	case 1031:  return "RPG Rocket Tube";
	case 1101:  return "SG Ammo";
	case 1102:  return "Rifle Ammo";
	case 1103:  return "SR Ammo";
	case 1104:  return "SMG Ammo";
	case 1105:  return "Pistol Ammo";
	case 1106:  return "RPG Ammo";
	case 1201:  return "Rifle Silencer";
	case 1202:  return "SR Silence";
	case 1204:  return "SMG Silencer";
	case 1211:  return "Rifle Compensator";
	case 1212:  return "SR Compensator";
	case 1213:  return "SMG Compensator";
	case 1221:  return "Rifle Flash Hider";
	case 1222:  return "SR Flash Hider";
	case 1223:  return "SMG Smoke Hider";
	case 1231:  return "SG Choke";
	case 1241:  return "Triangle Grip";
	case 1242:  return "Vertical Foregrip";
	case 1251:  return "Rifle QD-Mag";
	case 1252:  return "Rifle EX-Mag";
	case 1253:  return "Rifle EX-QD-Mag";
	case 1261:  return "SR Cheek Pad";
	case 1262:  return "Tactical Stock";
	case 1263:  return "SG Bullet Loop";
	case 1264:  return "SR EX-Mag";
	case 1265:  return "SR QD-Mag";
	case 1266:  return "SR EX-QD-Mag";
	case 1271:  return "Red Dot Sight";
	case 1272:  return "Holo-Sight";
	case 1273:  return "2x Scope";
	case 1274:  return "4x Scope";
	case 1275:  return "8x Scope";
	case 1276:  return "SMG QD-Mag";
	case 1277:  return "SMG EX-Mag";
	case 1278:  return "SMG QD-EX-Mag";
	case 1279:  return "Collapsible Stock";
	case 1303:  return "Crowbar";
	case 1306:  return "Frying Pan";
	case 1307:  return "Rubber Chicken";
	case 1401:  return "Grenade";
	case 1402:  return "Stun Grenade";
	case 1403:  return "Smoke Grenade";
	case 1404:  return "Molotov Cocktail";
	case 1405:  return "Chicken Grenade";
	case 1406:  return "Flash Grenade";

	default:return "no name";
		break;
	}
}

static void dieForever()
{
	if (!g_PresentHooked && !g_SetStreamSourceHooked &&
		!g_SetVertexShaderConstantFHooked && !g_SetTextureHooked &&
		!g_SetTransformHooked && !g_ResetHooked)
		return;

	DetourTransactionBegin();
	DetourUpdateThread(GetCurrentThread());

	if (g_SetStreamSourceHooked)
		DetourDetach(&(PVOID&)SetStreamSource_orig, SetStreamSource_hook);

	if (g_SetTextureHooked)
		DetourDetach(&(PVOID&)SetTexture_orig, SetTexture_hook);

	if (g_SetVertexShaderConstantFHooked)
		DetourDetach(&(PVOID&)SetVertexShaderConstantF_orig, SetVertexShaderConstantF_hook);

	if (g_SetTransformHooked)
		DetourDetach(&(PVOID&)SetTransform_orig, SetTransform_hook);

	if (g_DrawIndexedPrimitiveHooked)
		DetourDetach(&(PVOID&)DrawIndexedPrimitive_orig, DrawIndexedPrimitive_hook);

	if (g_ResetHooked)
		DetourDetach(&(PVOID&)Reset_orig, Reset_hook);

	if (g_PresentHooked)
		DetourDetach(&(PVOID&)Present_orig, Present_hook);

	LONG status = DetourTransactionCommit();
	if (status == NO_ERROR)
	{
		g_PresentHooked = false;
		g_SetStreamSourceHooked = false;
		g_SetVertexShaderConstantFHooked = false;
		g_SetTextureHooked = false;
		g_SetTransformHooked = false;
		g_DrawIndexedPrimitiveHooked = false;
		g_ResetHooked = false;
	}
}

//nSeven
void DrawBox(IDirect3DDevice9 *pDevice, float x, float y, float w, float h, D3DCOLOR Color)
{
	struct Vertex
	{
		float x, y, z, ht;
		DWORD Color;
	}
	V[4] = { { x, y + h, 0.0f, 0.0f, Color },{ x, y, 0.0f, 0.01f, Color },
	{ x + w, y + h, 0.0f, 0.0f, Color },{ x + w, y, 0.0f, 0.0f, Color } };
	pDevice->SetTexture(0, NULL);
	pDevice->SetPixelShader(0);
	pDevice->SetFVF(D3DFVF_XYZRHW | D3DFVF_DIFFUSE);
	pDevice->SetRenderState(D3DRS_ALPHABLENDENABLE, true);
	pDevice->SetRenderState(D3DRS_DESTBLEND, D3DBLEND_INVSRCALPHA);
	pDevice->SetRenderState(D3DRS_ZENABLE, FALSE);
	pDevice->SetRenderState(D3DRS_CULLMODE, D3DCULL_NONE);
	pDevice->DrawPrimitiveUP(D3DPT_TRIANGLESTRIP, 2, V, sizeof(Vertex));
}

class D3DTLVERTEX
{
public:
	FLOAT X, Y, X2, Y2;
	DWORD Color;
};
IDirect3DPixelShader9* oldppShader;

void DrawLine(IDirect3DDevice9* pDevice, float X, float Y, float X2, float Y2, float Width, D3DCOLOR Color)
{
	D3DTLVERTEX qV[2] = {
		{ (float)X , (float)Y, 0.0f, 1.0f, Color },
	{ (float)X2 , (float)Y2 , 0.0f, 1.0f, Color },
	};
	const DWORD D3DFVF_TL = D3DFVF_XYZRHW | D3DFVF_DIFFUSE | D3DFVF_TEX1;
	pDevice->SetRenderState(D3DRS_ALPHABLENDENABLE, true);
	pDevice->SetRenderState(D3DRS_DESTBLEND, D3DBLEND_INVSRCALPHA);
	pDevice->SetFVF(D3DFVF_TL);
	pDevice->SetTexture(0, NULL);
	pDevice->SetPixelShader(0);
	// FIX: qV only holds 2 vertices = 1 line. Passing 2 as PrimitiveCount made
	// D3D read 4 vertices and pull 2 junk vertices off the stack.
	pDevice->DrawPrimitiveUP(D3DPT_LINELIST, 1, qV, sizeof(D3DTLVERTEX));
}

void DrawFilledRect(int x, int y, int w, int h, D3DCOLOR color, IDirect3DDevice9* pDevice)
{
	if (w < 0)w = 1;
	if (h < 0)h = 1;
	if (x < 0)x = 1;
	if (y < 0)y = 1;
	// clamp absurd sizes: with bad offsets W2S can hand us garbage and
	// Clear() would wipe the ENTIRE backbuffer (the black-overlay bug).
	// Cap + skip off-screen (ported from process_monitor.cpp:887).
	if (w > 4096)w = 4096;
	if (h > 4096)h = 4096;
	if (x > 8192 || y > 8192) return;

	D3DRECT Rect = { x,y, x + w, y + h };
	pDevice->Clear(1, &Rect, D3DCLEAR_TARGET | D3DCLEAR_TARGET, color, NULL, NULL);
}

void DrawBorder(int x, int y, int w, int h, int px, D3DCOLOR border_col, IDirect3DDevice9* pDevice)
{
	DrawFilledRect(x, (y + h - px), w, px, border_col, pDevice);
	DrawFilledRect(x, y, px, h, border_col, pDevice);
	DrawFilledRect(x, y, w, px, border_col, pDevice);
	DrawFilledRect((x + w - px), y, px, h, border_col, pDevice);
}

static bool InsideCircle(int xc, int yc, int r, int x, int y)
{
	int dx = xc - x;
	int dy = yc - y;
	return dx * dx + dy * dy <= r * r;
}

void Box2D(D3DXVECTOR3 head, D3DXVECTOR3 root, DWORD dwColor, LPDIRECT3DDEVICE9 pDevice)
{
	D3DXVECTOR3 Box = head - root;
	if (Box.y < 0) Box.y *= -1;
	int BoxWidth = (int)Box.y / 2;
	int DrawX = (int)head.x - (BoxWidth / 2);
	int DrawY = (int)head.y;
	DrawBorder(DrawX, DrawY, BoxWidth, (int)Box.y, 2, dwColor, pDevice);
	DrawBorder(DrawX, DrawY, BoxWidth, (int)Box.y, 1, 0xFF000000, pDevice);
}

//hay , needle 
static bool findnew(string str1, string str2)
{
	if (strstr(str1.c_str(), str2.c_str()))
	{
		return true;
	}
	return false;
}

// ===== shared entity classifier (ESP + chams) ===============================
// Rejection tokens: loot, vehicles, weapons AND static map props (doors,
// blocks, trees...) can all live under the "character\..." namespace, so a
// bare prefix match is NOT enough for a player gate.
static const char* const kRejectTokens[] = {
	// gameplay objects that are never players
	"vehicle", "item", "weapon", "ClientWeaponEntity", "Plane",
	"DtsPlayerHeritage", "boat", "bike", "truck", "helicopter",
	"wheel", "parachute", "airdrop",
	// static map props - the "boxes on items/doors/vehicles" bug
	"door", "block", "wall", "tree", "rock", "grass", "prop",
	"static", "building", "furniture", "chair", "table", "barrel",
	"crate", "effect", "bullet", "grenade", "projectile",
	// loot that may not carry the "item" token in its 24-char name
	"backpack", "ammo", "medkit", "helmet", "vest", "loot"
};

static bool HasRejectToken(const string& nm)
{
	for (int i = 0; i < (int)(sizeof(kRejectTokens) / sizeof(kRejectTokens[0])); i++)
		if (findnew(nm, kRejectTokens[i])) return true;
	return false;
}

// Positive tokens that identify a player/bot body.
static bool HasPlayerToken(const string& nm)
{
	return findnew(nm, "character") || findnew(nm, "Robot") ||
		findnew(nm, "humanoid") || findnew(nm, "npc");
}

// TRUE only for names that identify a PLAYER or BOT and match no rejection
// token. Used by BOTH the ESP player gate and the DIP chams gate so the two
// can never disagree.
static bool IsPlayerName(const string& nm)
{
	if (nm.empty()) return false;
	if (!HasPlayerToken(nm)) return false;
	return !HasRejectToken(nm);
}

// Coarse per-entity kind for label/gate decisions (single source of truth).
enum EntKind { EK_NONE = 0, EK_PLAYER, EK_BOT, EK_ITEM, EK_VEHICLE,
	EK_WEAPON, EK_SUPPLY, EK_PLANE, EK_PROP };

static EntKind ClassifyEnt(const string& nm)
{
	if (nm.empty()) return EK_NONE;
	if (HasRejectToken(nm))
	{
		if (findnew(nm, "vehicle") || findnew(nm, "boat") || findnew(nm, "bike") ||
			findnew(nm, "truck") || findnew(nm, "helicopter") || findnew(nm, "wheel"))
			return EK_VEHICLE;
		if (findnew(nm, "Plane")) return EK_PLANE;
		if (findnew(nm, "DtsPlayerHeritage")) return EK_SUPPLY;
		if (findnew(nm, "weapon") || findnew(nm, "ClientWeaponEntity"))
			return EK_WEAPON;
		if (findnew(nm, "item") || findnew(nm, "backpack") || findnew(nm, "ammo") ||
			findnew(nm, "medkit") || findnew(nm, "helmet") || findnew(nm, "vest") ||
			findnew(nm, "loot") || findnew(nm, "grenade"))
			return EK_ITEM;
		return EK_PROP;
	}
	if (!HasPlayerToken(nm)) return EK_NONE;   // no positive token at all
	if (findnew(nm, "Robot") || findnew(nm, "humanoid") || findnew(nm, "npc"))
		return EK_BOT;
	if (findnew(nm, "character")) return EK_PLAYER;
	return EK_NONE;
}
D3DXVECTOR3 GetMidPoint(Vector3 V1, Vector3 V2)
{
	return D3DXVECTOR3((V1.x + V2.x) / 2, (V1.y + V2.y) / 2, (V1.z + V2.z) / 2);
}

static bool once = false;
static bool freee = true;

// ---------------------------------------------------------
// WORLD CHAIN AUTO-DETECT
// The 2026 x64 client is close to, but not guaranteed identical to, the 2018
// x86 client this hack came from. Try the known layout variants ONCE and cache
// whichever one actually resolves to a readable view matrix:
//   world : [base+OFFSET_PYGAME+0x410]  or  [[base+OFFSET_PYGAME]+0x410]
//   camera: qword/dword @ scene+4 or scene+8
//   matrix: camera+0xC4 / +0xC0 / +0xC8
// ---------------------------------------------------------
static int g_worldMode = 0; // 0 = unresolved, 1 = direct, 2 = pointer-global
static int g_camMode = 0;   // 0 = unresolved, 1 = q@+4, 2 = d@+4, 3 = q@+8, 4 = d@+8
static int g_matOff = 0;    // 0 = unresolved, else 0xC4 / 0xC0 / 0xC8

static bool MatReadable(uintptr_t addr)
{
	return Memory::ReadMemoryC<D3DXMATRIX>(addr);
}

static uintptr_t TryCamera(uintptr_t scene, D3DXMATRIX &outMatrix,
	bool haveIdx0, const D3DXVECTOR3 &idx0)
{
	uintptr_t q4 = Memory::ReadMemory<uintptr_t>(scene + 4);
	uintptr_t q8 = Memory::ReadMemory<uintptr_t>(scene + 8);
	uintptr_t cams[4] = { q4, (uintptr_t)Memory::ReadMemory<uint32_t>(scene + 4),
	                      q8, (uintptr_t)Memory::ReadMemory<uint32_t>(scene + 8) };
	int modes[4] = { 1, 2, 3, 4 };
	int matOffs[3] = { 0xC4, 0xC0, 0xC8 };

	// fast path: the combo that already proved itself (idx0 test at latch)
	if (g_matOff && g_camMode)
	{
		for (int i = 0; i < 4; i++)
		{
			if (modes[i] != g_camMode || cams[i] < 0x10000)
				continue;
			D3DXMATRIX cand = Memory::ReadMemory<D3DXMATRIX>(cams[i] + g_matOff);
			if (AcceptVP(cand, outMatrix, haveIdx0, idx0))
				return cams[i];
		}
		g_camMode = 0;   // latched combo went stale (zeros/freed/paused) ->
		g_matOff = 0;    // drop the latch and full-rescan below this frame
	}

	for (int m = 0; m < 3; m++)
	{
		for (int i = 0; i < 4; i++)
		{
			if (cams[i] < 0x10000 || cams[i] > 0x00007FFFFFFFFFFFULL)
				continue;
			// every candidate must pass the VP invariant AND - at latch
			// time - project the local player inside the viewport
			D3DXMATRIX cand = Memory::ReadMemory<D3DXMATRIX>(cams[i] + matOffs[m]);
			if (AcceptVP(cand, outMatrix, haveIdx0, idx0))
			{
				g_camMode = modes[i];
				g_matOff = matOffs[m];
				return cams[i];
			}
		}
	}
	return 0;
}

// Resolves ONLY the world pointer - variant detection no longer depends on
// the camera chain (which is broken in the x64 client). Variant 1 was
// verified live: base+OFFSET_PYGAME+0x410 == RVA 0x32C6688, the unique
// module qword that referenced the world object (entity count at +0x278).
static uintptr_t ResolveWorld()
{
	if (g_worldMode == 0)
	{
		// variant 1: [base + OFFSET_PYGAME + 0x410] -> world
		uintptr_t w = Memory::ReadMemory<uintptr_t>(BAddress + OFFSET_PYGAME + 0x410);
		if (w > 0x10000 && Memory::ReadMemory<uintptr_t>(w + 0x8) > 0x10000)
			g_worldMode = 1;
	}
	if (g_worldMode == 0)
	{
		// variant 2: [[base + OFFSET_PYGAME] + 0x410] -> world
		uintptr_t pg = Memory::ReadMemory<uintptr_t>(BAddress + OFFSET_PYGAME);
		if (pg > 0x10000)
		{
			uintptr_t w = Memory::ReadMemory<uintptr_t>(pg + 0x410);
			if (w > 0x10000 && Memory::ReadMemory<uintptr_t>(w + 0x8) > 0x10000)
				g_worldMode = 2;
		}
	}

	if (g_worldMode == 1)
		return Memory::ReadMemory<uintptr_t>(BAddress + OFFSET_PYGAME + 0x410);
	if (g_worldMode == 2)
	{
		uintptr_t pg = Memory::ReadMemory<uintptr_t>(BAddress + OFFSET_PYGAME);
		return (pg > 0x10000) ? Memory::ReadMemory<uintptr_t>(pg + 0x410) : 0;
	}
	return 0;
}

static uintptr_t ResolveWorldCamera(D3DXMATRIX &worldMatrix,
	bool haveIdx0, const D3DXVECTOR3 &idx0pos)
{
	uintptr_t world = ResolveWorld();
	if (world <= 0x10000)
		return 0;

	// ---- Priority 1: static VP from rosINTERNALesp_offsets.ini (fill the
	// RVA via injector\vpscan.ps1 while a match is running). ----
	if (OFFSET_VIEWMATRIX)
	{
		D3DXMATRIX m = Memory::ReadMemory<D3DXMATRIX>(BAddress + OFFSET_VIEWMATRIX);
		if (AcceptVP(m, worldMatrix, haveIdx0, idx0pos))
		{
			static bool loggedIni = false;
			if (!loggedIni)
			{
				char b[140];
				sprintf_s(b, "matrix source: memory VIEWMATRIX (ini RVA=0x%llX)",
					(unsigned long long)OFFSET_VIEWMATRIX);
				logInit(b);
				loggedIni = true;
			}
			return world;
		}
	}

	// ---- Priority 2: the 2018-proven memory chain world->scene(world+8)
	// ->camera(scene+4)->VP at +0xC4/+0xC0/+0xC8 - the ORIGINAL RosInfinity
	// source read exactly "worldMatrix = ReadMemory<D3DXMATRIX>(cameraBase
	// + 0xC4)" from MEMORY, never from shader uploads. Accepted via the VP
	// unit-vector invariant + the live idx0-on-screen latch. ----
	{
		uintptr_t scene = Memory::ReadMemory<uintptr_t>(world + 0x8);
		if (scene > 0x10000 && TryCamera(scene, worldMatrix, haveIdx0, idx0pos))
		{
			static bool loggedChain = false;
			if (!loggedChain)
			{
				char b[130];
				sprintf_s(b, "matrix source: camera chain +0x%03X (VP invariant + idx0 latch)", g_matOff);
				logInit(b);
				loggedChain = true;
			}
			return world;
		}
	}

	// Priority 3 (LAST RESORT ONLY): c0 upload stream. LIVE EVIDENCE THIS
	// IS NOT THE CAMERA VP (23:29-23:31 session): the latch picked
	// stream[20]/[21]/[24] on alternating frames (a real VP is ONE upload
	// per frame, never flapping between indices) with idx0 depth 49.6m
	// (the TPS camera rides 3-6m behind the local player) - c0 carries
	// PER-ENTITY WVPs, and projecting every entity through one of those
	// is what made boxes land on random geometry ("ESP attaches to
	// items", "aimbot jumps to items"). Used only when BOTH memory
	// sources above failed; every latch logs as VP-UNSAFE.
	{
		int best = -1;
		float bestD = 1.0e30f;
		bool bestCol = false;
		// LAYOUT LATCH (flicker fix): g_vpColVec was re-derived every frame and
		// idx0 passed both layouts on many frames, so row/col FLAPPED per frame
		// and the boxes jumped. Once proven, only accept candidates matching
		// the proven layout (fallback to re-derivation is impossible - if none
		// match, we simply keep the previous VP below).
		bool layoutLocked = g_vpIdx0Checked;
		for (unsigned i = 0; i < g_vpFrameN; i++)
		{
			D3DXMATRIX cand;
			memcpy(&cand, g_vpFrame[i], sizeof(cand));
			if (!IsVPShape(cand) || IsIdentityMatrix(cand))
				continue;
			if (haveIdx0 && g_vpW > 0 && g_vpH > 0)
			{
				bool col = false;
				if (!Idx0PassesVP(cand, idx0pos, (int)g_vpW, (int)g_vpH, &col))
					continue;
				if (layoutLocked && col != g_vpColVec)
					continue;                      // locked layout wins
				D3DXVECTOR3 s; float w = 0;
				ProjectThroughVP(cand, idx0pos, (int)g_vpW, (int)g_vpH, s, w, col);
				float dx = s.x - g_vpW * 0.5f, dy = s.y - g_vpH * 0.5f;
				float d = dx * dx + dy * dy;
				// stable tie-break: depth proximity to the TPS camera (the real
				// VP keeps idx0 at 3-30m => w 30..300dm; shadow passes are km)
				if (w < 500.0f) d -= 1.0e6f;   // <50m bonus (depth already sanity-capped)
				if (d < bestD) { bestD = d; best = (int)i; bestCol = col; }
			}
			else if (best < 0 && !layoutLocked)
			{
				best = (int)i;          // structural-only fallback (no idx0 pos)
				bestCol = g_vpIdx0Checked ? g_vpColVec : false;
			}
		}
		// NO idx0 proof this frame -> hold the LAST PROVEN VP instead of
		// grabbing stream[0] (the "structural-only" frames are what made the
		// ESP re-place itself onto random geometry every few seconds).
		if (best < 0 && g_hasLastVP)
		{
			memcpy(&worldMatrix, &g_lastVP, sizeof(worldMatrix));
			g_vpColVec = g_lastVPCol;
			return world;
		}
		if (best >= 0)
		{
			memcpy(&worldMatrix, g_vpFrame[best], sizeof(worldMatrix));
			g_vpColVec = bestCol;
			if (haveIdx0)
				g_vpIdx0Checked = true;
			memcpy(&g_lastVP, &worldMatrix, sizeof(g_lastVP));
			g_lastVPCol = g_vpColVec;
			g_hasLastVP = true;
			static int lastBest = -1;
			static ULONGLONG lastLog = 0;
			ULONGLONG now = GetTickCount64();
			if (best != lastBest && now - lastLog > 2000)
			{
				lastBest = best;
				lastLog = now;
				char b[180];
				if (haveIdx0)
				{
					D3DXVECTOR3 s; float w = 0;
					ProjectThroughVP(worldMatrix, idx0pos, (int)g_vpW, (int)g_vpH,
						s, w, g_vpColVec);
					sprintf_s(b, "VP-UNSAFE: c0 stream[%d] idx0->(%.0f,%.0f) depth=%.1fm layout=%s",
						best, s.x, s.y, w / 10.0f, g_vpColVec ? "col" : "row");
				}
				else
					sprintf_s(b, "VP-UNSAFE: c0 stream[%d] structural-only (idx0 pos unknown)", best);
				logInit(b);
			}
			return world;
		}
	}

	// (The memory VIEWMATRIX + camera-chain priorities were MOVED to the
	// TOP of this function - they must be tried BEFORE the c0 stream.)

	// The old SetTransform and SVSCF-c0 fallbacks were REMOVED: SetTransform
	// only ever saw identity in this client and SVSCF c0 projected idx0
	// offscreen in every run - both fed garbage into w2s. Returning 0 makes
	// drawesp HOLD with an explicit log instead of drawing lies.
	return 0;
}

// ---- world-position readers (drawesp) -------------------------------------
static bool SaneT(float x, float y, float z)
{
	if (x != x || y != y || z != z) return false;
	if (fabsf(x) > 100000.0f || fabsf(y) > 100000.0f || fabsf(z) > 100000.0f) return false;
	// at least TWO meaningful components: the live probe showed the model's
	// 0x310 window reads as a CONFIG value (0, 2.5, 0)-style constants,
	// which passed the old sum>1 test and stacked every box at ONE bogus
	// world point - the "ESP attached to items / aim jumps to items" bug.
	int nz = 0;
	if (fabsf(x) > 0.5f) nz++;
	if (fabsf(y) > 0.5f) nz++;
	if (fabsf(z) > 0.5f) nz++;
	return nz >= 2;
}

// Model world matrix -> entity translation. Layouts: row-major translation
// at m[12..14]; TRANSPOSED at m[3,7,11] - both flagged by m[15] == 1.
// Ground truth: ros_infinity_validate.txt "[pos] CALIBRATED world matrix @
// model+0x310 (2/32 models) [transposed]"; discover.h default vote 0x3B0.
static bool ReadWorldPos(uintptr_t model, D3DXVECTOR3& out)
{
	// 0x3B0 FIRST: the ORIGINAL RosInfinity source (2018, same engine family)
	// reads exactly "ReadMemory<D3DXMATRIX>(r_pModel + 0x3B0)" and projects
	// m[12..14] - it is the proven world-matrix offset. 0x310 (calibrated on
	// 2/32 models on this build) is second; anything else must pass the same
	// affine + sane-translation gate (a wrong offset practically never
	// yields m[15]==1.0 with a sane nonzero translation).
	// ALL FOUR candidates are tried (the loop used to run k<2, which made
	// 0x3A0/0x3C0 dead code despite the comment promising them as backup).
	static const int offs[4] = { 0x3B0, 0x310, 0x3A0, 0x3C0 };
	for (int k = 0; k < 4; k++)
	{
		D3DXMATRIX m = Memory::ReadMemory<D3DXMATRIX>(model + offs[k]);
		const float* f = &m._11;
		if (fabsf(f[15] - 1.0f) > 0.01f)
			continue;                       // not an affine transform
		if (SaneT(f[12], f[13], f[14])) { out = D3DXVECTOR3(f[12], f[13], f[14]); return true; }
		if (SaneT(f[3], f[7], f[11]))   { out = D3DXVECTOR3(f[3], f[7], f[11]);  return true; }
	}
	return false;
}

// r4 upload = the entity's REAL world matrix (SVSCF "start=4 n=4 M D":
// rotation rows + row4 translation (-212,-73,266) w=1) - affine gate only.
static bool SeqAffinePos(const float* m, D3DXVECTOR3& out)
{
	if (fabsf(m[15] - 1.0f) > 0.01f)
		return false;
	if (SaneT(m[12], m[13], m[14])) { out = D3DXVECTOR3(m[12], m[13], m[14]); return true; }
	if (SaneT(m[3], m[7], m[11]))   { out = D3DXVECTOR3(m[3], m[7], m[11]);  return true; }
	return false;
}

void drawesp(IDirect3DDevice9* pDevice)
{
	if (opt.options.reset)
	{
		dieForever();
	}
	// main ESP master - aimbot/Exit-Cheat must work even with ESP off, so
	// drawesp() now runs for those too and gates visuals with espOn.
	const bool espOn = opt.d3d.esp != 0;

	// Only OFFSET_PYGAME is required for the world chain. OFFSET_LOCALPLAYER is
	// optional (the entity loop overwrites MyPosition from the first entity).
	if (OFFSET_PYGAME == 0)
	{
		static bool loggedOffsetsOnce = false;
		if (!loggedOffsetsOnce)
		{
			logInit("drawesp: OFFSET_PYGAME is 0 - run locate_offsets.ps1 (Admin) or fill in InitializeOffsets(). ESP disabled.");
			loggedOffsetsOnce = true;
		}
		return;
	}

	// VP + positions are resolved AFTER the pool read (idx0 = pool[0] is the
	// live latch proof for the camera VP - see the block below the pool).

	// ---- entity pool: baked + LIVE-VALIDATED 10/05 (discover.h constants) ----
	// world obj RVA 0x2D30530, vector {begin,end} at +0x808/+0x810;
	// names via animator = model+0x3B8 -> char* at +0x8. Live samples:
	//   [0] "character\dataosha_femal" (local player), [1..] "vehicle\boat1\..."
	// Position pipeline (validated by probe + SVSCF this session): the model
	// object carries NO inline transform (0x310 = config window with
	// constants like (0,2.5,0); 0x3B0/0x3A0/0x3C0 = zero), so positions
	// come from the r4 upload sequence (real world matrices, SVSCF
	// "start=4 n=4"), paired to the pool by index (validate.txt: r4=54
	// pool=55 -> MAPPED, idx0 at screen center). Memory ReadWorldPos is a
	// tightened secondary only; unpaired = SKIPPED.
	uintptr_t poolObj = BAddress + 0x2D30530;
	uintptr_t pBegin = Memory::ReadMemory<uintptr_t>(poolObj + 0x808);
	uintptr_t pEnd = Memory::ReadMemory<uintptr_t>(poolObj + 0x810);
	int visibleCount = 0;
	if (pBegin > 0x10000 && pEnd > pBegin && (pEnd - pBegin) % 8 == 0 && (pEnd - pBegin) < 0x8000)
		visibleCount = (int)((pEnd - pBegin) / 8);
	if (visibleCount <= 0 || visibleCount > 4096)
	{
		static bool loggedPoolOnce = false;
		if (!loggedPoolOnce) { logInit("drawesp: entity pool empty (world+0x808) - waiting for match"); loggedPoolOnce = true; }
		return;
	}
	// pool-count stability gate: during match transitions the begin/end
	// pair flaps (94->10->1) and entity reads then hit freed memory.
	// The count must read the SAME on two consecutive frames first.
	{
		static int g_poolLastCnt = -1;
		if (visibleCount != g_poolLastCnt)
		{
			g_poolLastCnt = visibleCount;
			return;
		}
		g_poolN = visibleCount;
	}
	{
		static bool loggedPoolOnce2 = false;
		if (!loggedPoolOnce2)
		{
			char pb[100];
			sprintf_s(pb, "entity pool LIVE: %d entities (world+0x808)", visibleCount);
			logInit(pb);
			loggedPoolOnce2 = true;
		}
	}
	// ---- position source accounting: r4 upload (pool-index paired,
	// validate.txt "r4=54 pool=55 -> MAPPED") first; model memory only as
	// secondary with the tightened 2-component gate; unpaired entities are
	// SKIPPED - no garbage boxes. ----
	const float(*seqM)[16] = g_wmFrame;
	unsigned seqN = g_wmFrameN;
	int posMem = 0, posSeq = 0, posMiss = 0;

	// ---- VP latch: idx0 = local player = pool[0], taken from the
	// draw-time map (his own pinned matrix when drawn this frame). ----
	D3DXVECTOR3 idx0pos;
	bool haveIdx0 = false;
	{
		if (g_drawnF[0])
			haveIdx0 = SeqAffinePos(g_drawPosF[0], idx0pos);
		if (!haveIdx0)
		{
			uintptr_t m0 = Memory::ReadMemory<uintptr_t>(pBegin);
			if (m0 > 0x10000)
				haveIdx0 = ReadWorldPos(m0, idx0pos);
		}
	}
	D3DXMATRIX worldMatrix;
	uintptr_t m_pWorld = ResolveWorldCamera(worldMatrix, haveIdx0, idx0pos);
	{
		static ULONGLONG lastVpLog = 0;
		if (!m_pWorld && GetTickCount64() - lastVpLog > 5000)
		{
			lastVpLog = GetTickCount64();
			char vb[140];
			sprintf_s(vb, "VP unresolved: camera chain/ini failed (haveIdx0=%d) - holding ESP",
				haveIdx0 ? 1 : 0);
			logInit(vb);
		}
	}
	if (!m_pWorld)
		return;

	D3DXVECTOR3 vScreen;
	pDevice->GetViewport(&Viewport);
	int width = (int)Viewport.Width;
	int height = (int)Viewport.Height;
	// aimbot: best target = closest to crosshair inside a SCREEN-
	// PROPORTIONAL FOV. The old fixed 30px radius was effectively never
	// satisfied in real play, so the lock never fired.
	const float fovR = ((width < height) ? (float)width : (float)height) * 0.35f;
	const float fovR2 = fovR * fovR;
	float bestAimX = 0.0f, bestAimY = 0.0f, bestAimD2 = 1.0e12f;

	// ---- audit buckets (rate-limited "espaudit:" beacon): accepted
	// player/bot names; "character\..." names the classifier REJECTED;
	// accepted players that had NO world position (the old code dropped
	// them before the name was even read, so a position bug could hide
	// behind a clean audit). ----
	static std::vector<std::string> g_auP, g_auR, g_auN;
	static ULONGLONG g_auTick = 0;

	// ---- draw counters (rate-limited "espdraw:" beacon): each sub-option
	// proves its wiring by its counter going 0 <-> N when toggled ----
	static int g_dLbl = 0, g_dBox2 = 0, g_dBox3 = 0, g_dLine = 0, g_dDist = 0,
		g_dHp = 0, g_dItem = 0, g_dVeh = 0, g_dType = 0, g_dBadP = 0,
		g_dMissP = 0, g_dAim = 0;

	for (int i = 0; i < visibleCount; i++)
	{
		uintptr_t r_pModel = Memory::ReadMemory<uintptr_t>(pBegin + (uintptr_t)i * sizeof(uintptr_t));
		if (r_pModel < 0x10000)
			continue;

		// ---- 1) IDENTITY FIRST: name + kind are resolved before anything
		// else so classification, audit and the position-less-player
		// counter can never be skipped by a missing matrix. One classifier
		// (ClassifyEnt / IsPlayerName) serves ESP AND chams. ----
		uintptr_t m_pAnimator = Memory::ReadMemory<uintptr_t>(r_pModel + 0x3B8);
		string str = (m_pAnimator > 0x10000)
			? Memory::ReadString(Memory::ReadMemory<uintptr_t>(m_pAnimator + 0x8), 24)
			: string();
		const EntKind kind = ClassifyEnt(str);
		const bool isPlayer = (kind == EK_PLAYER || kind == EK_BOT);
		const bool isBot = (kind == EK_BOT);

		// ---- 2) POSITION: PRIMARY = the draw-time map (this DIP's own
		// pinned matrix, chams-validated identity). Memory secondary;
		// not drawn this frame AND no memory pos = SKIP. ----
		D3DXVECTOR3 wpos;
		bool posOk = false;
		if (i < 4096 && g_drawnF[i] && SeqAffinePos(g_drawPosF[i], wpos))
		{
			posOk = true;
			posSeq++;
		}
		else if (ReadWorldPos(r_pModel, wpos))
		{
			posOk = true;
			posMem++;
		}
		if (!posOk)
		{
			posMiss++;
			// an identified player WITHOUT a position is an ESP miss on a
			// real target - record the name so the hole is visible in-log
			if (isPlayer && !str.empty())
			{
				g_dMissP++;
				if (g_auN.size() < 8)
				{
					bool dup = false;
					for (size_t k = 0; k < g_auN.size(); k++)
						if (g_auN[k] == str) { dup = true; break; }
					if (!dup) g_auN.push_back(str);
				}
			}
			continue;
		}

		// ---- 3) PROJECTION through the latched camera VP. Head MUST
		// project - the old feet-100px fallback fabricated box heights and
		// drew full-screen garbage. Screen height of the box is sanity
		// checked before any box/aim may use it. ----
		D3DXVECTOR3 feet, headS;
		float w0 = 0.0f, wHead = 0.0f;
		if (!ProjectThroughVP(worldMatrix, wpos, width, height, feet, w0, g_vpColVec))
			continue;                               // behind camera / absurd
		if (!ProjectThroughVP(worldMatrix, wpos + D3DXVECTOR3(0, 21.5f, 0),
			width, height, headS, wHead, g_vpColVec))
		{
			g_dBadP++;
			continue;
		}
		vScreen = feet;
		const float boxH = feet.y - headS.y;        // px; >0 = upright
		const bool bhOk = (boxH >= 3.0f && boxH <= 0.92f * (float)height);

		// player-gate audit: distinct accepted names + distinct REJECTED
		// names that still claim "character" (each bucket capped at 16)
		if (!str.empty() && (isPlayer || findnew(str, "character")))
		{
			std::vector<std::string>& b = isPlayer ? g_auP : g_auR;
			if (b.size() < 16)
			{
				bool dup = false;
				for (size_t k = 0; k < b.size(); k++)
					if (b[k] == str) { dup = true; break; }
				if (!dup) b.push_back(str);
			}
		}

		if (i == 0)
		{
			// diag: idx0 = local player, his own WVP must land near center
			static ULONGLONG lastDiag = 0;
			static int diagN = 0;
			ULONGLONG tn = GetTickCount64();
			if (diagN < 4 && tn - lastDiag > 4000)
			{
				diagN++; lastDiag = tn;
				bool okc = (vScreen.x >= 0.0f && vScreen.y >= 0.0f &&
					vScreen.x < (float)width && vScreen.y < (float)height);
				char db[200];
				sprintf_s(db, "w2s diag: idx0 %s/%s -> %s (%.0f,%.0f) depth=%.0f | seq=%u+%u pool=%d distinct c4=%d c0=%d",
					g_entStream ? "c0" : "c4", g_entColMode ? "col4" : "row4",
					okc ? "ONSCREEN" : "offscreen", vScreen.x, vScreen.y, w0,
					g_wmFrameN, g_vpFrameN, visibleCount, g_lastDist4, g_lastDist0);
				logInit(db);
			}
			continue;
		}
		// sentinel culling (black-screen guard): vScreen was computed above
		// directly from this entity's own WVP.
		if (vScreen.x >= 0.0f && vScreen.y >= 0.0f &&
			vScreen.x < (float)width && vScreen.y < (float)height)
		{
			if (isPlayer)
			{
				// "Player ESP" master toggle: labels/boxes/lines/dist/health
				// all answer to it (it used to gate ONLY the BOT label, so
				// turning Player ESP OFF still showed full player ESP).
				const bool pvis = espOn && opt.espopt.player;
				if (pvis)
				{
					DrawString(font, vScreen.x, vScreen.y - 20,
						isBot ? GREEN(255) : RED(255), (PCHAR)(isBot ? "BOT" : "PLAYER"));
					g_dLbl++;
				}

				if (pvis && opt.espopt.lines)
				{
					DrawLine(pDevice, (float)(width / 2) - 1, 10, vScreen.x, vScreen.y, 20, D3DCOLOR_ARGB(255, 0, 255, 255));
					g_dLine++;
				}

				D3DXVECTOR3 pRoot = vScreen;
				D3DXVECTOR3 pHead = headS;  // feet + head both via the real VP
				float dist2 = w0 / 10.0f;   // view depth (dm) -> metres, old scale
				if (pvis && opt.espopt.box3 && bhOk)
				{
					// Proper screen-space 3D box from the projected head/root
					// rect: front face = silhouette, back face sheared up-right
					// by a DEPTH-PROPORTIONAL fraction. The old bone1..8 wire
					// carried a hardcoded -38px shift that floated the "bones"
					// above the player whenever he was far (box shrinks, 38px
					// doesn't) - the source of the misplaced blue lines.
					float top = pHead.y, bot = pRoot.y;
					float cx = (pHead.x + pRoot.x) * 0.5f;
					float bh = bot - top;
					if (bh < 8.0f) bh = 8.0f;
					float bw = bh * 0.42f;
					float dx = bh * 0.22f, dy = bh * 0.12f;
					float l = cx - bw * 0.5f, r = cx + bw * 0.5f;
					float l2 = l + dx, r2 = r + dx, t2 = top - dy, b2 = bot - dy;
					// front face
					DrawLine(pDevice, l, top, r, top, 1, BLUE(255));
					DrawLine(pDevice, r, top, r, bot, 1, BLUE(255));
					DrawLine(pDevice, r, bot, l, bot, 1, BLUE(255));
					DrawLine(pDevice, l, bot, l, top, 1, BLUE(255));
					// back face (sheared)
					DrawLine(pDevice, l2, t2, r2, t2, 1, BLUE(255));
					DrawLine(pDevice, r2, t2, r2, b2, 1, BLUE(255));
					DrawLine(pDevice, r2, b2, l2, b2, 1, BLUE(255));
					DrawLine(pDevice, l2, b2, l2, t2, 1, BLUE(255));
					// connectors
					DrawLine(pDevice, l, top, l2, t2, 1, BLUE(255));
					DrawLine(pDevice, r, top, r2, t2, 1, BLUE(255));
					DrawLine(pDevice, r, bot, r2, b2, 1, BLUE(255));
					DrawLine(pDevice, l, bot, l2, b2, 1, BLUE(255));
					g_dBox3++;
				}
				
				if (pvis && opt.espopt.box2 && bhOk)
				{
					Box2D(pHead, pRoot, WHITE(255), pDevice);
					g_dBox2++;
				}

				if (opt.d3d.aimbot && bhOk)
				{
					// Track for the post-loop action: aim at the upper
					// chest (15% below the head top) inside a screen-
					// proportional FOV - the old 30px radius never fired.
					const float ax = (pHead.x + pRoot.x) * 0.5f;
					const float ay = pHead.y + boxH * 0.15f;
					const float adx = ax - width * 0.5f;
					const float ady = ay - height * 0.5f;
					const float d2 = adx * adx + ady * ady;
					if (d2 <= fovR2 && d2 < bestAimD2)
					{
						bestAimD2 = d2;
						bestAimX = ax;
						bestAimY = ay;
					}
				}
				if (pvis && opt.espopt.dist)
				{
					char result[24];
					sprintf_s(result, "%.1f m", dist2);
					DrawString(font, vScreen.x, vScreen.y - 10, WHITE(255), (PCHAR)"%s", result);
					g_dDist++;
				}
				
				// HEALTH CHAIN AUDIT (live-verified via RC hex.read): the 2018
				// chain (entity+0x100 -> +0x14 -> +0x98 -> +0x8) has a NULL
				// first hop on this x64 build (entity+0x100 == 0 for EVERY
				// character, lobby AND match). Old code still dereferenced the
				// whole chain -> 3 failing RPM calls per player per frame and
				// num6 always 0. Guard it: skip the chain on NULL and clamp
				// garbage. Bars show only when a real value arrives.
				int num6 = 0;
				if (pvis && opt.espopt.health)   // chain reads only when bars will draw
				{
					uintptr_t hp1 = Memory::ReadMemory<uintptr_t>(r_pModel + 256);
					if (hp1 > 0x10000)
					{
						uintptr_t hp2 = Memory::ReadMemory<uintptr_t>(hp1 + 20);
						uintptr_t hp3 = hp2 > 0x10000 ? Memory::ReadMemory<uintptr_t>(hp2 + 152) : 0;
						if (hp3 > 0x10000)
							num6 = Memory::ReadMemory<int>(hp3 + 8);
					}
					if (num6 < 0 || num6 > 1000) num6 = 0;  // garbage must not print bars
				}
				
                if (pvis && opt.espopt.health)
				{
					// ONE string per draw: the old 12-line ladder painted at
					// the SAME pixel bottom-up, so the smallest bar always
					// overwrote the real value (always showed a single "+").
					if (num6 >= 1)
					{
						int bars = num6 / 10;
						if (bars > 10) bars = 10;
						char hp[12];
						memset(hp, '+', bars);
						hp[bars] = '\0';
						D3DCOLOR hc = num6 >= 80 ? GREEN(255)
							: num6 >= 50 ? YELLOW(255)
							: num6 >= 25 ? ORANGE(255) : RED(255);
						DrawString(font, vScreen.x - 10, vScreen.y + 15, hc, (PCHAR)"%s", hp);
						g_dHp++;
					}
				}
			}
			else if (espOn)
			{
				// Non-player labels: each answers to ITS OWN sub-toggle and
				// raw names only under "Unknown Entity Type". Dynamic
				// strings always go through "%s" - a raw name used as a
				// format string is a latent crash if it contains '%'.
				if (kind == EK_ITEM && opt.espopt.item)
				{
					DrawString(font, vScreen.x, vScreen.y, YELLOW(255), (PCHAR)"ITEM");
					g_dItem++;
				}
				else if (kind == EK_VEHICLE && opt.espopt.vehicle)
				{
					DrawString(font, vScreen.x, vScreen.y, BLUE(255), (PCHAR)"VEHICLE");
					g_dVeh++;
				}
				else if (kind == EK_PLANE && opt.espopt.vehicle)
				{
					DrawString(font, vScreen.x, vScreen.y, BLUE(255), (PCHAR)"PLANE");
					g_dVeh++;
				}
				else if (kind == EK_SUPPLY && opt.espopt.item)
				{
					DrawString(font, vScreen.x, vScreen.y, YELLOW(255), (PCHAR)"SUPPLY");
					g_dItem++;
				}
				else if (kind == EK_WEAPON && opt.espopt.item)
				{
					DrawString(font, vScreen.x, vScreen.y, BLACK(100), (PCHAR)"WEAPON");
					g_dItem++;
				}
				else if (opt.espopt.type && !str.empty())
				{
					DrawString(font, vScreen.x, vScreen.y, WHITE(255), (PCHAR)"%s", str.c_str());
					g_dType++;
				}
			}
		}
	}

	// player-gate audit beacon (5s): accepted vs rejected vs position-less
	{
		ULONGLONG tn = GetTickCount64();
		if (tn - g_auTick > 5000 && (!g_auP.empty() || !g_auR.empty() || !g_auN.empty()))
		{
			g_auTick = tn;
			std::string p, r, n;
			for (size_t k = 0; k < g_auP.size(); k++) { if (k) p += ","; p += g_auP[k]; }
			for (size_t k = 0; k < g_auR.size(); k++) { if (k) r += ","; r += g_auR[k]; }
			for (size_t k = 0; k < g_auN.size(); k++) { if (k) n += ","; n += g_auN[k]; }
			char ab[600];
			sprintf_s(ab, "espaudit: accept=[%s] reject=[%s] nopos=[%s]",
				p.c_str(), r.c_str(), n.c_str());
			logInit(ab);
			g_auP.clear();
			g_auR.clear();
			g_auN.clear();
		}
	}

	// draw-counter beacon (5s): one line proves every sub-option's wiring
	// (toggle OFF -> counter stays 0 with entities on screen; ON -> counts)
	{
		static ULONGLONG lastDrawLog = 0;
		ULONGLONG tn = GetTickCount64();
		if (tn - lastDrawLog > 5000)
		{
			lastDrawLog = tn;
			char db[260];
			sprintf_s(db, "espdraw: lbl=%d b2=%d b3=%d ln=%d ds=%d hp=%d item=%d veh=%d type=%d pmiss=%d badp=%d aimf=%d",
				g_dLbl, g_dBox2, g_dBox3, g_dLine, g_dDist, g_dHp,
				g_dItem, g_dVeh, g_dType, g_dMissP, g_dBadP, g_dAim);
			logInit(db);
			g_dLbl = g_dBox2 = g_dBox3 = g_dLine = g_dDist = g_dHp = 0;
			g_dItem = g_dVeh = g_dType = g_dMissP = g_dBadP = g_dAim = 0;
		}
	}

	// position-source telemetry (5s): how many entities got a REAL world
	// position from their own model matrix vs skipped (no matrix).
	{
		static ULONGLONG lastPosLog = 0;
		if (GetTickCount64() - lastPosLog > 5000)
		{
			lastPosLog = GetTickCount64();
			char pb[160];
			sprintf_s(pb, "pos: r4=%d mem=%d skip=%d pool=%d/%u junk=%u | VP %s%s idx0pos=%d",
				posSeq, posMem, posMiss, visibleCount, seqN, g_r4junk,
				m_pWorld ? "latched" : "FAIL", g_vpColVec ? "(col)" : "(row)",
				haveIdx0 ? 1 : 0);
			logInit(pb);
		}
	}

	// ---- aimbot: act on the SINGLE best target inside the screen FOV with
	// SMOOTH RELATIVE mouse motion. Replaces the old 30px radius + absolute
	// SetCursorPos: the radius was effectively never satisfied so the lock
	// never fired, and absolute cursor warps fight both raw-input mice and
	// the OS cursor. Relative deltas converge in a few frames, work for
	// absolute and raw mouse modes, are foreground-guarded, and are capped
	// so a bad projection can never fling the camera. ----
	if (opt.d3d.aimbot && bestAimD2 < 1.0e11f)
	{
		DrawLine(pDevice, bestAimX, bestAimY, width / 2.0f, height - 15.0f, 20, RED(255));
		bool ownWnd = false;
		if (HWND fg = GetForegroundWindow())
		{
			DWORD wndPid = 0;
			GetWindowThreadProcessId(fg, &wndPid);
			ownWnd = (wndPid == GetCurrentProcessId());
		}
		const bool aimKey = (GetAsyncKeyState(VK_LSHIFT) & 0x8000) != 0;
		if (aimKey && ownWnd)
		{
			float dx = (bestAimX - width * 0.5f) * 0.45f;
			float dy = (bestAimY - height * 0.5f) * 0.45f;
			if (dx > 150.0f) dx = 150.0f; else if (dx < -150.0f) dx = -150.0f;
			if (dy > 150.0f) dy = 150.0f; else if (dy < -150.0f) dy = -150.0f;
			if (dx > 0.5f || dx < -0.5f || dy > 0.5f || dy < -0.5f)
			{
				mouse_event(MOUSEEVENTF_MOVE, (DWORD)(int)dx, (DWORD)(int)dy, 0, 0);
				g_dAim++;
				static ULONGLONG lastAimLog = 0;
				if (GetTickCount64() - lastAimLog > 2000)
				{
					lastAimLog = GetTickCount64();
					char ab[150];
					sprintf_s(ab, "aim: lock off=(%+.0f,%+.0f)px fov=%.0f gain=0.45 key=LSHIFT",
						bestAimX - width * 0.5f, bestAimY - height * 0.5f, fovR);
					logInit(ab);
				}
			}
		}
	}
}

// ===== Fast Drop / No Recoil (ported from process_monitor's scan+patch)
// FastDrop: CE group {450, 109.5445098877, 20, 450} f32x4 -> write 2500.
// NoRecoil: doubles == 1.3 -> write 0.1. ALL writes guarded: current value
// must equal the expectation or the write is refused + logged.
struct EnvScanState
{
	bool started, done, fallLogged, recoilWarned;
	uintptr_t fall[16];        // ALL writable float-group instances, expected 450.0
	int fallN;
	int fallSkipped;           // read-only (image default) hits we REFUSED to patch
	int fallSelf;              // hits inside OUR dll (the memcmp literal) - excluded
	uintptr_t recoil[16];      // doubles, expected 1.3 (diagnostic only now)
	int recoilN;
};
static EnvScanState g_env = {};

// Our OWN module range: the scan pattern {450,109.5445,20,450} is embedded
// in THIS DLL's .rdata (it's the literal we memcmp against). Live probing
// (fdprobe) proved the ONLY process-wide hit is that read-only self-match -
// the game does NOT contain the pattern at all. Scanning our own bytes
// produced a fake "1 instance FOUND" that could never be written. Exclude it.
static uintptr_t g_selfLo = 0, g_selfHi = 0;
static void MarkSelfModule()
{
	HMODULE self = NULL;
	if (GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS | GET_MODULE_HANDLE_EX_FLAG_UNCHANGED_REFCOUNT,
		(LPCSTR)&MarkSelfModule, &self) && self)
	{
		MODULEINFO mi = {};
		if (GetModuleInformation(GetCurrentProcess(), self, &mi, sizeof(mi)))
		{
			g_selfLo = (uintptr_t)mi.lpBaseOfDll;
			g_selfHi = g_selfLo + mi.SizeOfImage;
		}
	}
}
static bool InSelfModule(uintptr_t a){ return g_selfLo && a >= g_selfLo && a < g_selfHi; }

static DWORD WINAPI EnvScanThread(LPVOID)
{
	MarkSelfModule();
	SIZE_T got = 0;
	unsigned char dos[0x40];
	if (!ReadProcessMemory(processHandle, (LPCVOID)BAddress, dos, 0x40, &got) || got != 0x40)
	{ logInit("envscan: DOS hdr unreadable"); g_env.done = true; return 0; }
	int32_t e_lfanew = *(int32_t*)(dos + 0x3C);
	unsigned char fh[0x18];
	if (!ReadProcessMemory(processHandle, (LPCVOID)(BAddress + e_lfanew), fh, 0x18, &got))
	{ logInit("envscan: PE hdr unreadable"); g_env.done = true; return 0; }
	uint16_t numSec = *(uint16_t*)(fh + 6);
	uint16_t sizeOpt = *(uint16_t*)(fh + 20);
	uintptr_t secTab = BAddress + e_lfanew + 24 + sizeOpt;
	uintptr_t dataStart = 0, dataEnd = 0;
	for (int i = 0; i < numSec; i++)
	{
		unsigned char sh[40];
		if (!ReadProcessMemory(processHandle, (LPCVOID)(secTab + i * 40), sh, 40, &got)) break;
		if (memcmp(sh, ".data", 5) == 0)
		{
			dataStart = BAddress + *(uint32_t*)(sh + 12);
			dataEnd = dataStart + *(uint32_t*)(sh + 8);
		}
	}
	static const float seq[4] = { 450.0f, 109.5445098877f, 20.0f, 450.0f };
	// WRITABILITY FILTER: the pattern exists in the image both as the live
	// config AND as read-only defaults (.rdata). The old scan took the first
	// hit in either -> WPM to the read-only copy failed silently every frame
	// and the 5s check kept reporting "REVERTED to 450". Only collect
	// candidates on READWRITE pages; verify with an actual probe write of the
	// CURRENT value (no semantic change, just proves the page accepts writes).
	auto writable = [&](uintptr_t addr) -> bool {
		MEMORY_BASIC_INFORMATION mbi;
		if (VirtualQueryEx(processHandle, (LPCVOID)addr, &mbi, sizeof(mbi)) != sizeof(mbi))
			return false;
		DWORD p = mbi.Protect & 0xFF;
		return mbi.State == MEM_COMMIT &&
			(p == PAGE_READWRITE || p == PAGE_WRITECOPY || p == PAGE_EXECUTE_READWRITE || p == PAGE_EXECUTE_WRITECOPY);
	};
	auto probeWrite = [&](uintptr_t addr) -> bool {
		float cur = 0; SIZE_T w = 0;
		if (!ReadProcessMemory(processHandle, (LPCVOID)addr, &cur, sizeof(cur), &w) || w != sizeof(cur))
			return false;
		return WriteProcessMemory(processHandle, (LPVOID)addr, &cur, sizeof(cur), &w) && w == sizeof(cur);
	};
	if (dataStart && dataEnd > dataStart)
	{
		size_t len = (size_t)(dataEnd - dataStart);
		unsigned char* buf = (unsigned char*)malloc(len);
		if (buf && ReadProcessMemory(processHandle, (LPCVOID)dataStart, buf, len, &got) && (size_t)got == len)
		{
			for (size_t i = 0; i + 16 <= len && g_env.fallN < 16; i += 4)
				if (memcmp(buf + i, seq, 16) == 0)
				{
					uintptr_t a = dataStart + i;
					if (InSelfModule(a)) { g_env.fallSelf++; continue; }  // our own constant
					if (writable(a) && probeWrite(a))
						g_env.fall[g_env.fallN++] = a;
					else g_env.fallSkipped++;
				}
			double one3 = 1.3;
			for (size_t i = 0; i + 8 <= len && g_env.recoilN < 16; i += 8)
				if (memcmp(buf + i, &one3, 8) == 0)
					g_env.recoil[g_env.recoilN++] = dataStart + i;
		}
		if (buf) free(buf);
	}
	else logInit("envscan: .data not found (runtime headers)");

	// Heap/region fallback: walk ALL committed readable memory (any mapping
	// type - config may be private heap OR mapped), 1MB chunks, 15-byte
	// overlap. Previous bugs fixed: VQ failure used to BREAK the whole scan,
	// MEM_PRIVATE-only filter could skip mapped config, no walk telemetry.
	// THIS PASS ALSO SKIPS READ-ONLY PAGES (same writability rule as above).
	unsigned long walkR = 0; double walkMB = 0;
	if (g_env.fallN == 0 || g_env.recoilN < 16)
	{
		SYSTEM_INFO si; GetSystemInfo(&si);
		// writable pages ONLY - read-only hits get refused by the probe below
		const DWORD rmask = PAGE_READWRITE | PAGE_WRITECOPY | PAGE_EXECUTE_READWRITE | PAGE_EXECUTE_WRITECOPY;
		MEMORY_BASIC_INFORMATION mbi;
		const SIZE_T CH = 1 << 20;
		unsigned char* cb = (unsigned char*)malloc(CH);
		uintptr_t prevA = 0;
		for (uintptr_t a = (uintptr_t)si.lpMinimumApplicationAddress;
			cb && a < (uintptr_t)si.lpMaximumApplicationAddress; a += mbi.RegionSize)
		{
			memset(&mbi, 0, sizeof(mbi));
			if (VirtualQueryEx(processHandle, (LPCVOID)a, &mbi, sizeof(mbi)) != sizeof(mbi) || mbi.RegionSize == 0)
			{
				if (a <= prevA) break;        // no forward progress -> real stop
				prevA = a; a += 0x10000 - mbi.RegionSize; continue;   // hop 64KB
			}
			prevA = a;
			if (mbi.State != MEM_COMMIT || (mbi.Protect & (PAGE_GUARD | PAGE_NOACCESS))) continue;
			if (!(mbi.Protect & rmask)) continue;
			walkR++;
			walkMB += (double)mbi.RegionSize / (1024.0 * 1024.0);
			uintptr_t rs = (uintptr_t)mbi.BaseAddress, re = rs + mbi.RegionSize;
			uintptr_t cs = rs;
			while (cs < re)
			{
				SIZE_T want = CH; if (cs + want > re) want = re - cs;
				SIZE_T got2 = 0;
				if (ReadProcessMemory(processHandle, (LPCVOID)cs, cb, want, &got2) && got2 >= 16)
				{
					if (g_env.fallN < 16)
						for (SIZE_T i = 0; i + 16 <= got2 && g_env.fallN < 16; i += 4)
							if (memcmp(cb + i, seq, 16) == 0)
							{
								uintptr_t a = cs + i;
								if (InSelfModule(a)) { g_env.fallSelf++; continue; }
								if (writable(a) && probeWrite(a))
									g_env.fall[g_env.fallN++] = a;
								else g_env.fallSkipped++;
							}
					if (g_env.recoilN < 16)
					{
						double one3 = 1.3;
						for (SIZE_T i = 0; i + 8 <= got2 && g_env.recoilN < 16; i += 8)
							if (memcmp(cb + i, &one3, 8) == 0)
								g_env.recoil[g_env.recoilN++] = cs + i;
					}
				}
				if (got2 <= 16) { cs += (got2 ? got2 : 0x10000); continue; }
				cs += got2 - 15;
				if (g_env.fallN && g_env.recoilN >= 16) break;
			}
			if (g_env.fallN && g_env.recoilN >= 16) break;
		}
		if (cb) free(cb);
	}

	char b[250];
	if (g_env.fallN)
		sprintf_s(b, "envscan done: fastdrop %d writable instance(s) FOUND (%d read-only, %d self-module skipped), norecoil=%d cand(s)",
			g_env.fallN, g_env.fallSkipped, g_env.fallSelf, g_env.recoilN);
	else
		sprintf_s(b, "envscan done: fastdrop NOT in game memory (%d read-only, %d self-module skipped) - signature absent on this build, norecoil=%d cand(s)",
			g_env.fallSkipped, g_env.fallSelf, g_env.recoilN);
	logInit(b);
	g_env.done = true;
	return 0;
}

// Called every Present: cheap unless a feature just toggled on.
static void ApplyEnvFeatures()
{
	if ((opt.d3d.fastdrop || opt.d3d.norecoil) && !g_env.started && BAddress)
	{
		g_env.started = true;
		logInit("envscan: background FastDrop/NoRecoil scan starting...");
		CreateThread(NULL, 0, EnvScanThread, NULL, 0, NULL);
	}

	// ---- Fast Drop: 450 -> 2500 over ALL found instances (guarded each)
	if (g_env.fallN)
	{
		if (opt.d3d.fastdrop)
		{
			int wrote = 0, refused = 0, failed = 0;
			for (int i = 0; i < g_env.fallN; i++)
			{
				float cur = Memory::ReadMemory<float>(g_env.fall[i]);
				if (cur == 450.0f || cur == 2500.0f)
				{
					float v = 2500.0f; SIZE_T w = 0;
					// CHECK the write: an unchecked WPM failure looked exactly
					// like "game rewrites it" in the 5s log (it never landed).
					if (WriteProcessMemory(processHandle, (LPVOID)g_env.fall[i], &v, sizeof(v), &w) && w == sizeof(v))
						wrote++;
					else
						failed++;
				}
				else refused++;
			}
			if (!g_env.fallLogged)
			{
				g_env.fallLogged = true;
				char b[220];
				MEMORY_BASIC_INFORMATION mbi;
				memset(&mbi, 0, sizeof(mbi));
				const char* rgn = "?";
				if (VirtualQuery((LPCVOID)g_env.fall[0], &mbi, sizeof(mbi)) == sizeof(mbi))
					rgn = (mbi.Type == MEM_PRIVATE) ? "MEM_PRIVATE"
						: (mbi.Type == MEM_IMAGE) ? "MEM_IMAGE" : "MEM_MAPPED";
				sprintf_s(b, "fastdrop: patched %d/%d instance(s) to 2500 (%d refused, %d WPM-FAILED) | addr=0x%llX region=%s size=0x%llX",
					wrote, g_env.fallN, refused, failed, (unsigned long long)g_env.fall[0],
					rgn, (unsigned long long)mbi.RegionSize);
				logInit(b);
				// WHICH module owns this address? (ros64.exe .data = likely
				// the real physics constant; some other DLL = wrong target)
				HMODULE fh = NULL;
				if (GetModuleHandleExA(GET_MODULE_HANDLE_EX_FLAG_FROM_ADDRESS,
					(LPCSTR)g_env.fall[0], &fh) && fh)
				{
					char mp[MAX_PATH] = { 0 }, mb2[190];
					GetModuleFileNameA(fh, mp, MAX_PATH);
					const char* bn = strrchr(mp, '\\');
					bn = bn ? bn + 1 : mp;
					sprintf_s(mb2, "fastdrop: instance inside %s+0x%llX", bn,
						(unsigned long long)((uintptr_t)g_env.fall[0] - (uintptr_t)fh));
					logInit(mb2);
				}
			}
		}
		else
		{
			for (int i = 0; i < g_env.fallN; i++)
			{
				float cur = Memory::ReadMemory<float>(g_env.fall[i]);
				if (cur == 2500.0f)
				{ float v = 450.0f; SIZE_T w = 0; WriteProcessMemory(processHandle, (LPVOID)g_env.fall[i], &v, sizeof(v), &w); }
			}
		}
	}

	// ---- FastDrop persistence check (5s): does the game write 450 back?
	// (proves the patch target is actually the live physics value or not)
	if (opt.d3d.fastdrop && g_env.fallN && g_env.done)
	{
		static ULONGLONG fdChk = 0;
		if (GetTickCount64() - fdChk > 5000)
		{
			fdChk = GetTickCount64();
			// read back what WE wrote: if still 2500 the patch lands and the
			// physics value simply isn't this address; if 450, either the game
			// rewrites it or (pre-fix) WPM silently failed.
			float cur = Memory::ReadMemory<float>(g_env.fall[0]);
			char fb[130];
			sprintf_s(fb, "fastdrop: value=%.0f %s", cur,
				cur == 2500.0f ? "HELD (patch active; verify in-game)" :
				(cur == 450.0f ? "REVERTED to 450 (game rewrites it)" : "CHANGED by game"));
			logInit(fb);
		}
	}

	// ---- No Recoil: writes HELD. The 1.3 constant is a SHARED
	// recoil/SPEED multiplier on this build - patching all 8-16 candidates
	// (observed live) also nerfed movement to baby-steps. Keep until a
	// recoil-only address is isolated by targeted RE.
	if (opt.d3d.norecoil && g_env.done && !g_env.recoilWarned)
	{
		g_env.recoilWarned = true;
		char b[170];
		sprintf_s(b, "norecoil: HELD - 1.3 also controls movement speed (%d candidate(s)); writing it caused baby-steps", g_env.recoilN);
		logInit(b);
	}
}

cMenu Menu;
copt opt;
cSound Sound;

float ScreenCenterX = 0.0f;
float ScreenCenterY = 0.0f;

void PreReset(LPDIRECT3DDEVICE9 pDevice)
{
	Menu.PreReset();
	return;
}

void PostReset(LPDIRECT3DDEVICE9 pDevice)
{
	Menu.PostReset(pDevice);
	return;
}

LPD3DXFONT Font;
static cMenu mensu;

HRESULT CreateMyShader(IDirect3DPixelShader9 **pShader, IDirect3DDevice9 *Device, float red, float green, float blue, float alpha)
{
	ID3DXBuffer *MyBuffer = NULL;
	char MyShader[256];
	sprintf(MyShader, "ps.1.1\ndef c0, %f, %f, %f, %f\nmov r0,c0", red / 255, green / 255, blue / 255, alpha / 255);
	D3DXAssembleShader(MyShader, sizeof(MyShader), NULL, NULL, 0, &MyBuffer, NULL);
	if (FAILED(Device->CreatePixelShader((const DWORD*)MyBuffer->GetBufferPointer(), pShader)))return E_FAIL;
	return S_OK;
}

HRESULT APIENTRY Present_hook(LPDIRECT3DDEVICE9 pDevice, CONST RECT* pSourceRect, CONST RECT* pDestRect, HWND hDestWindowOverride, CONST RGNDATA* pDirtyRegion) {
	// snapshot the entity-position stream BEFORE our own menu/ESP drawing
	// (font/sprite calls could append constants and shift the pool mapping)
	g_wmFrameN = g_wmSeqN <= 1024 ? g_wmSeqN : 1024;
	memcpy(g_wmFrame, g_wmSeqA, (size_t)g_wmFrameN * sizeof(g_wmSeqA[0]));
	g_wmSeqN = 0;
	// snapshot the draw-time entity map for drawesp (same render thread)
	memcpy(g_drawPosF, g_drawPos, sizeof(g_drawPos));
	memcpy(g_drawnF, g_drawnLive, sizeof(g_drawnLive));
	memset(g_drawnLive, 0, sizeof(g_drawnLive));
	g_vpFrameN = g_vpSeqN <= 1024 ? g_vpSeqN : 1024;
	memcpy(g_vpFrame, g_vpSeqA, (size_t)g_vpFrameN * sizeof(g_vpSeqA[0]));
	g_vpSeqN = 0;

	// draw-order beacon (5s): the (streamIdx:poolName) sequence proves
	// whether r4 order == pool order (monotonic), has culled gaps, or is
	// scrambled - the deciding evidence for the pairing fix.
	{
		static ULONGLONG lastDseq = 0;
		if (g_drawSeq[0] && GetTickCount64() - lastDseq > 5000)
		{
			lastDseq = GetTickCount64();
			char db2[760];
			sprintf_s(db2, "drawseq: n=%u aff=%u junk=%u pool=%d | %.660s",
				g_drawSeqN, g_wmFrameN, g_r4junk, g_poolN, g_drawSeq);
			logInit(db2);
			g_drawSeq[0] = 0;
			g_drawSeqN = 0;
		}
		g_lastRecIdx = -1;   // new frame: first draw of each entity counts again
	}

	// distinct-row4 counting: a PER-ENTITY stream yields ~N distinct
	// matrices/frame; a shared view/VP stream yields ~1 (the screenshot's
	// stacked labels = shared stream). Then auto-select stream + origin
	// convention (row4=row-vector, col4=column-vector) via idx0-center test.
	{
		auto distinctRow4 = [](const float(*s)[16], unsigned n) -> int {
			int d = 0;
			for (unsigned i = 0; i < n; i++)
			{
				bool seen = false;
				for (unsigned j = 0; j < i && !seen; j++)
					if ((int)(s[i][12] * 4) == (int)(s[j][12] * 4) &&
						(int)(s[i][13] * 4) == (int)(s[j][13] * 4) &&
						(int)(s[i][15] * 4) == (int)(s[j][15] * 4)) seen = true;
				if (!seen) d++;
			}
			return d;
		};
		g_lastDist4 = distinctRow4(g_wmFrame, g_wmFrameN);
		g_lastDist0 = distinctRow4(g_vpFrame, g_vpFrameN);

		if (g_entStream < 0)
		{
			bool ok4 = g_wmFrameN >= 8 && g_lastDist4 * 10 >= (int)g_wmFrameN * 6;
			bool ok0 = g_vpFrameN >= 8 && g_lastDist0 * 10 >= (int)g_vpFrameN * 6;
			if (ok4 || ok0)
			{
				int bestS = ok4 ? 0 : 1, bestMode = 0;
				float bestD = 1.0e30f;
				for (int s = 0; s < 2; s++)
				{
					if (s == 0 && !ok4) continue;
					if (s == 1 && !ok0) continue;
					const float(*m)[16] = (s == 0) ? g_wmFrame : g_vpFrame;
					for (int mode = 0; mode < 2; mode++)
					{
						float cw, cxp, cyp;
						if (mode == 0) { cw = m[0][15]; cxp = m[0][12]; cyp = m[0][13]; }
						else           { cw = m[0][11]; cxp = m[0][3];  cyp = m[0][7]; }
						if (cw <= 0.05f || cw > 100000.0f) continue;
						float sx = g_vpW > 0 ? (g_vpW * 0.5f * (cxp / cw) + g_vpW * 0.5f) : -1.0e6f;
						float sy = g_vpH > 0 ? (g_vpH * 0.5f - g_vpH * 0.5f * (cyp / cw)) : -1.0e6f;
						float dx = sx - g_vpW * 0.5f, dy = sy - g_vpH * 0.5f;
						float dist = dx * dx + dy * dy;
						if (dist < bestD) { bestD = dist; bestS = s; bestMode = mode; }
					}
				}
				g_entStream = bestS;
				g_entColMode = bestMode;
				char sb[190];
				sprintf_s(sb, "entity stream: %s origin=%s | distinct c4=%d/%u c0=%d/%u | idx0 centerErr=%.0fpx",
					bestS ? "c0" : "c4", bestMode ? "col4" : "row4",
					g_lastDist4, g_wmFrameN, g_lastDist0, g_vpFrameN,
					sqrtf(bestD));
				logInit(sb);
			}
		}
	}

	if (font == NULL)
		D3DXCreateFont(pDevice, 14, 0, FW_BOLD, 0, FALSE, DEFAULT_CHARSET, OUT_DEFAULT_PRECIS, DEFAULT_QUALITY, DEFAULT_PITCH | FF_DONTCARE, TEXT("Italic"), &font);

	if (xdxd)
	{
		id = GetCurrentProcessId();
		processHandle = OpenProcess(PROCESS_ALL_ACCESS, FALSE, id);
		BAddress = (uintptr_t)GetModuleHandle(NULL);

        // Initialize our dynamic offsets here
        InitializeOffsets();

		// Save/Load settings path: dlldir was NEVER initialized (only a
		// commented-out copy in CBase.cpp), so "settings.ini" resolved
		// relative to ros64's CWD - which the launcher changes - and
		// Save/Load silently wrote/read different files (or failed).
		// Pin it to %TEMP%, same directory as the crash-proof log.
		{
			char tmpDir[300] = { 0 };
			if (GetTempPathA(300, tmpDir) > 0)
				sprintf_s(dlldir, sizeof(dlldir), "%s", tmpDir);
			char sp[360];
			sprintf_s(sp, "settings path: %ssettings.ini", dlldir);
			logInit(sp);
		}

		xdxd = false;
	}

	if (!Tools.Init)
	{
		D3DXCreateLine(pDevice, &Tools.pLine);
		Tools.Init = TRUE;
	}

	// ===== black-screen fix: snapshot ALL device state before our overlay
	// (ported from process_monitor.cpp:2115). CreateStateBlock(D3DSBT_ALL)
	// records the game's state; Capture() refreshes it every frame and
	// Apply() right before Present_orig undoes every PS/FVF/blend change
	// we make below - without it our state leaks into the game's next
	// frame (flicker/hitches).
	if (!g_OverlayStateBlock && FAILED(pDevice->CreateStateBlock(D3DSBT_ALL, &g_OverlayStateBlock)))
		g_OverlayStateBlock = NULL;
	if (g_OverlayStateBlock) g_OverlayStateBlock->Capture();

	// ---- overlay render-state normalization ------------------------------
	// DrawBox/DrawText are XYZRHW screen-space draws but inherit whatever
	// render state the game's LAST pass left active. If the game leaves
	// scissor-test/Z-test/stencil on (or a non-backbuffer RT bound) at
	// Present time, our overlay is clipped or discarded -> fully invisible
	// even though the hook runs and SHOW=1. Fix before drawing: bind the
	// backbuffer (saving the original RT - state blocks don't capture RTs)
	// and force a plain 2D state. Every render state below is captured by
	// the D3DSBT_ALL state block, so Apply() before Present restores them.
	{
		IDirect3DSurface9* rt = NULL;
		IDirect3DSurface9* bb = NULL;
		pDevice->GetRenderTarget(0, &rt);
		pDevice->GetBackBuffer(0, 0, D3DBACKBUFFER_TYPE_MONO, &bb);
		int sameRT = (rt && bb && rt == bb) ? 1 : 0;

		// periodic diagnostic: snapshot the game's leftover state BEFORE we
		// change it, so the log reveals the actual clipping cause.
		static ULONGLONG lastDiag = 0;
		if (GetTickCount64() - lastDiag > 5000)
		{
			lastDiag = GetTickCount64();
			DWORD scis = 0, zen = 0, sten = 0;
			pDevice->GetRenderState(D3DRS_SCISSORTESTENABLE, &scis);
			pDevice->GetRenderState(D3DRS_ZENABLE, &zen);
			pDevice->GetRenderState(D3DRS_STENCILENABLE, &sten);
			D3DVIEWPORT9 vp = { 0 };
			pDevice->GetViewport(&vp);
			char db[176];
			sprintf_s(db, "diag: font=%d sb=%d sameRT=%d scissor=%u z=%u stencil=%u vp=%ux%u",
				font ? 1 : 0, g_OverlayStateBlock ? 1 : 0, sameRT,
				scis, zen, sten, vp.Width, vp.Height);
			logInit(db);
		}

		// if the game left a non-backbuffer RT bound, draw where Present reads
		if (!sameRT && bb)
		{
			if (g_prevOverlayRT) { g_prevOverlayRT->Release(); g_prevOverlayRT = NULL; }
			g_prevOverlayRT = rt;   // keep our ref to restore after drawing
			rt = NULL;
			pDevice->SetRenderTarget(0, bb);
		}
		if (rt) rt->Release();
		if (bb) bb->Release();

		pDevice->SetRenderState(D3DRS_SCISSORTESTENABLE, FALSE);
		pDevice->SetRenderState(D3DRS_ZENABLE, FALSE);
		pDevice->SetRenderState(D3DRS_ZWRITEENABLE, FALSE);
		pDevice->SetRenderState(D3DRS_STENCILENABLE, FALSE);
		pDevice->SetRenderState(D3DRS_CULLMODE, D3DCULL_NONE);
		pDevice->SetRenderState(D3DRS_ALPHATESTENABLE, FALSE);
	}

	PostReset(pDevice);      // creates the menu font once (font == NULL check inside)
	Menu.ShowMenu(pDevice);  // INSERT toggles SHOW in here

	// FIX: PreReset(pDevice) used to run here, right after drawing. It destroys
	// the menu font, so the old code recreated (and leaked) a CD3DFont on EVERY
	// Present. It is now called from Reset_hook() when the D3D device is
	// actually reset (alt-tab, resolution change, ...).

	static bool loggedPresentOnce = false;
	if (!loggedPresentOnce)
	{
		logInit("Present_hook is running: D3D9 hooks are live.");
		loggedPresentOnce = true;
	}

	pDevice->GetViewport(&Tools.g_ViewPort);
	g_vpW = Tools.g_ViewPort.Width;   // cache for the SVS-triggered probe
	g_vpH = Tools.g_ViewPort.Height;
	ScreenCenterX = (float)Tools.g_ViewPort.Width / 2;
	ScreenCenterY = (float)Tools.g_ViewPort.Height / 2;

	if (opt.d3d.cross)
	{
		Tools.FillRGB(ScreenCenterX - 14, ScreenCenterY, 10, 1, D3DXCOLOR(1.0, 0.0, 0.0, 1.0), pDevice);//Left line
		Tools.FillRGB(ScreenCenterX + 5, ScreenCenterY, 10, 1, D3DXCOLOR(1.0, 0.0, 0.0, 1.0), pDevice);//Right line
		Tools.FillRGB(ScreenCenterX, ScreenCenterY - 14, 1, 10, D3DXCOLOR(1.0, 0.0, 0.0, 1.0), pDevice);//Top line
		Tools.FillRGB(ScreenCenterX, ScreenCenterY + 5, 1, 10, D3DXCOLOR(1.0, 0.0, 0.0, 1.0), pDevice);//Bottom line
		Tools.DrawCircle(D3DXVECTOR2(ScreenCenterX, ScreenCenterY), 8, 60, D3DXCOLOR(1.0, 0.0, 0.0, 1.0));//Circle
		Tools.DrawPoint(ScreenCenterX, ScreenCenterY, 1, 1, D3DXCOLOR(0.0, 1.0, 0.0, 1.0), pDevice);//Point
	}
	// Exit Cheat must work regardless of ESP/Aimbot state (drawesp() is only
	// reached when one of them is ON - reset used to silently do nothing).
	if (opt.options.reset)
		dieForever();

	// ESP master OR aimbot: the aimbot target search lives in drawesp(), so
	// it used to silently die whenever the ESP master toggle was OFF.
	if (opt.d3d.esp || opt.d3d.aimbot)
		drawesp(pDevice);

	// ---- draw-time ESP markers (Stage 1 v2): label = "group:vSize",
	// green = c4, cyan = c12, yellow = other group. The group that keeps
	// moving on screen is this build's real WVP register. ----
	if (!g_telMark.empty())
	{
		int drawn = 0;
		for (size_t i = 0; i < g_telMark.size() && drawn < 15; i++, drawn++)
		{
			int mx = (int)g_telMark[i].x, my = (int)g_telMark[i].y;
			D3DCOLOR col;
			if (g_telMark[i].src == 4)       col = D3DCOLOR_ARGB(255, 0, 255, 0);
			else if (g_telMark[i].src == 12) col = D3DCOLOR_ARGB(255, 0, 255, 255);
			else                             col = D3DCOLOR_ARGB(255, 255, 255, 0);
			DrawBorder(mx - 7, my - 7, 14, 14, 1, col, pDevice);
			if (font)
			{
				char lab[24];
				sprintf_s(lab, "c%u:%u", g_telMark[i].src, g_telMark[i].vSize);
				DrawString(font, mx + 7, my - 7, col, lab);
			}
		}
		g_telMark.clear();
	}
	// ---- telemetry: once per 5s while ESP is on. "moves" per register
	// start = in-viewport AND moved since last sample - a real camera WVP
	// moves constantly, frozen UI matrices stay at 0. sss/dip/st audit
	// which draw-entry hooks this engine actually uses in-match. ----
	ApplyEnvFeatures();
	{
		// OPTION-STATE beacon: prints EVERY main+sub toggle every 5s so the
		// audit can confirm each menu action actually changed the variable
		// the feature gates on (log-driven option verification).
		static ULONGLONG lastOpt = 0;
		if (GetTickCount64() - lastOpt > 5000)
		{
			lastOpt = GetTickCount64();
			char ob[240];
			sprintf_s(ob, "OPTS cross=%d esp=%d chams=%d aim=%d fd=%d nr=%d | player=%d item=%d veh=%d type=%d dist=%d box2=%d box3=%d lines=%d health=%d | cham a=%d r=%d g=%d b=%d",
				opt.d3d.cross, opt.d3d.esp, opt.d3d.Chams, opt.d3d.aimbot, opt.d3d.fastdrop, opt.d3d.norecoil,
				opt.espopt.player, opt.espopt.item, opt.espopt.vehicle, opt.espopt.type, opt.espopt.dist,
				opt.espopt.box2, opt.espopt.box3, opt.espopt.lines, opt.espopt.health,
				opt.chamsopt.alpha, opt.chamsopt.red, opt.chamsopt.green, opt.chamsopt.blue);
			logInit(ob);
		}
	}
	{
		// r4pos beacon (5s): the actual affine world translations captured
		// this frame + c0 camera candidates. probe3.ps1 matches these
		// against memory floats to FIND the per-entity position offset.
		static ULONGLONG lastR4p = 0;
		if (GetTickCount64() - lastR4p > 5000)
		{
			lastR4p = GetTickCount64();
			char rb[430];
			int o = sprintf_s(rb, "r4pos: n=%u junk=%u |", g_wmFrameN, g_r4junk);
			int shown = 0;
			for (unsigned i = 0; i < g_wmFrameN && shown < 8; i++)
			{
				const float* m = g_wmFrame[i];
				if (!R4AffineGate(m)) continue;
				float tx, ty, tz;
				if (R4SaneT(m[12], m[13], m[14])) { tx = m[12]; ty = m[13]; tz = m[14]; }
				else                              { tx = m[3];  ty = m[7];  tz = m[11]; }
				// dedupe: the same rig matrix uploads dozens of times per
				// frame and drowned the beacon (all-identical refs made the
				// brute-force probe match only d3d9 staging copies).
				bool dup = false;
				for (unsigned j = 0; j < i && !dup; j++)
				{
					const float* mj = g_wmFrame[j];
					if (!R4AffineGate(mj)) continue;
					float jx, jy, jz;
					if (R4SaneT(mj[12], mj[13], mj[14])) { jx = mj[12]; jy = mj[13]; jz = mj[14]; }
					else                                 { jx = mj[3];  jy = mj[7];  jz = mj[11]; }
					if (fabsf(jx - tx) < 2.0f && fabsf(jy - ty) < 2.0f &&
						fabsf(jz - tz) < 2.0f) dup = true;
				}
				if (dup) continue;
				o += sprintf_s(rb + o, sizeof(rb) - o, " (%.1f,%.1f,%.1f)", tx, ty, tz);
				shown++;
			}
			// c0 camera candidates: identity-rotation world matrices in the
			// VP stream (SVSCF saw "1 0 0|0 1 0 0|0 0 1 0|(10866,-964,-768)")
			int cam = 0;
			for (unsigned i = 0; i < g_vpFrameN && cam < 2; i++)
			{
				const float* m = g_vpFrame[i];
				if (fabsf(m[15] - 1.0f) > 0.01f) continue;
				if (fabsf(m[0] - 1.0f) > 0.01f || fabsf(m[5] - 1.0f) > 0.01f ||
					fabsf(m[10] - 1.0f) > 0.01f) continue;
				if (fabsf(m[1]) + fabsf(m[2]) + fabsf(m[4]) + fabsf(m[6]) +
					fabsf(m[8]) + fabsf(m[9]) > 0.01f) continue;
				if (!R4SaneT(m[12], m[13], m[14])) continue;
				o += sprintf_s(rb + o, sizeof(rb) - o, " cam(%.1f,%.1f,%.1f)",
					m[12], m[13], m[14]);
				cam++;
			}
			logInit(rb);
		}
	}
	{
		// VB pointer beacon: distinct stream-0 VBs bound at this frame's
		// uploads (probe5 matches these VALUES inside pool model objects
		// -> VB->entity map = draw-time identity without order guesses).
		static ULONGLONG lastVb = 0;
		if (GetTickCount64() - lastVb > 5000)
		{
			lastVb = GetTickCount64();
			char vbb[400];
			int o = sprintf_s(vbb, "vbptrs: n=%u:", g_wmFrameN);
			int shown = 0;
			for (unsigned i = 0; i < g_wmFrameN && shown < 8; i++)
			{
				bool dup = false;
				for (unsigned j = 0; j < i; j++)
					if (g_wmVB[j] == g_wmVB[i]) { dup = true; break; }
				if (dup || !g_wmVB[i]) continue;
				o += sprintf_s(vbb + o, sizeof(vbb) - o, " 0x%llX",
					(unsigned long long)(uintptr_t)g_wmVB[i]);
				shown++;
			}
			o += sprintf_s(vbb + o, sizeof(vbb) - o, " last0=0x%llX",
				(unsigned long long)(uintptr_t)g_lastVB0);
			logInit(vbb);
		}
	}
	{
		// menu open/close telemetry: proves INSERT handling live
		static int lastShow = -1;
		int nowShow = Menu.SHOW ? 1 : 0;
		if (lastShow == -1) lastShow = nowShow;
		else if (nowShow != lastShow)
		{
			lastShow = nowShow;
			char mb[64];
			sprintf_s(mb, "menu: SHOW=%d", nowShow);
			logInit(mb);
		}
	}
	{
		static ULONGLONG lastTel = 0;
		ULONGLONG now = GetTickCount64();
		if (opt.d3d.esp && now - lastTel > 5000)
		{
			lastTel = now;
			char pick[40];
			if (g_entStream < 0)
				sprintf_s(pick, "none d4=%d d0=%d", g_lastDist4, g_lastDist0);
			else
				sprintf_s(pick, "%s%s d4=%d d0=%d", g_entStream ? "c0" : "c4",
					g_entColMode ? "+col4" : "+row4", g_lastDist4, g_lastDist0);
			char tbuf[700];
			int o = sprintf_s(tbuf, "TEL st=%u vs=%u sss=%u dip=%u att=%u pick=%s r4j=%u rs=%u pool=%d | moves:",
				g_telST, g_vsSeen, g_sss, g_telDip, g_wvpAttTotal, pick, g_r4junk, g_rigSkip, g_poolN);
			for (int g = 0; g <= 28; g += 4)
				o += sprintf_s(tbuf + o, sizeof(tbuf) - o, " c%d=%u", g, g_wvpMov[g]);
			// any OTHER start (incl. unaligned c13!) that moved - capped
			int extra = 0;
			for (int g = 0; g < 256 && extra < 12; g++)
				if (g_wvpMov[g] && (g % 4 != 0 || g > 28))
				{
					o += sprintf_s(tbuf + o, sizeof(tbuf) - o, " c%d=%u", g, g_wvpMov[g]);
					extra++;
				}
			o += sprintf_s(tbuf + o, sizeof(tbuf) - o, " | push=%u", g_telPushed);
			if (g_telVN)
			{
				o += sprintf_s(tbuf + o, sizeof(tbuf) - o, " v:");
				for (int i = 0; i < g_telVN && o < 640; i++)
					o += sprintf_s(tbuf + o, sizeof(tbuf) - o, " %u:%u", g_telV[i], g_telVC[i]);
			}
			logInit(tbuf);
			for (int i = 0; i < g_telVN; i++) g_telVC[i] = 0;
			g_telPushed = 0;
			g_telST = g_vsSeen = g_sss = g_telDip = 0;
			g_wvpAttTotal = 0;
			for (int g = 0; g < 256; g++) { g_wvpAtt[g] = 0; g_wvpMov[g] = 0; }
			// g_wvpLx/Ly intentionally kept: moved-detection needs history
		}
	}

	// restore the game's original RT if we redirected it (state blocks don't
	// capture RTs, so Apply() below won't do this for us)
	if (g_prevOverlayRT)
	{
		pDevice->SetRenderTarget(0, g_prevOverlayRT);
		g_prevOverlayRT->Release();
		g_prevOverlayRT = NULL;
	}
	// restore the game's state exactly as we found it (undo PS=NULL/FVF/blend)
	if (g_OverlayStateBlock) g_OverlayStateBlock->Apply();

	return Present_orig(pDevice, pSourceRect, pDestRect, hDestWindowOverride, pDirtyRegion); // return anywhere in this function crash xD
}

HRESULT APIENTRY Reset_hook(IDirect3DDevice9* pDevice, D3DPRESENT_PARAMETERS *pPresentationParameters)
{
	// state block belongs to the old device - drop it, next Present recreates
	if (g_OverlayStateBlock)
	{
		g_OverlayStateBlock->Release();
		g_OverlayStateBlock = NULL;
	}

	// FIX: `font` is the ID3DXFont actually used by the ESP. The old code tested
	// `Font` (capital F) which is never assigned, so the ESP font was never
	// notified of device loss/reset.
	if (font)
		font->OnLostDevice();

	if (Tools.pLine)
		Tools.pLine->OnLostDevice();

	PreReset(pDevice); // release menu (CD3DFont) resources before the reset

	HRESULT ResetReturn = Reset_orig(pDevice, pPresentationParameters);

	if (SUCCEEDED(ResetReturn))
	{
		if (font)
			font->OnResetDevice();
		if (Tools.pLine)
			Tools.pLine->OnResetDevice();

		PostReset(pDevice); // recreate the menu font on the reset device
	}

	return ResetReturn;
}

class Renderer
{
public:
	class RenderInfo
	{
	public:
		char _0x0000[48];
		__int32 m_FrameCounter; //0x0030 
	};

	char _0x0000[8];
	RenderInfo* m_pRenderInfo; //0x0008 
	char _0x000C[56];
	__int32 m_Width; //0x0044 
	__int32 m_Height; //0x0048 
	char _0x004C[68];
	__int32 m_PrimCount; //0x0090 
	__int32 m_ModelPrimCount; //0x0094 
	__int32 m_ModelDPCount; //0x0098 
	char _0x009C[44];
	float m_LogicFPS; //0x00C8 
	float m_RenderFPS; //0x00CC 

	static Renderer* GetInstance()
	{
		uintptr_t uBase = reinterpret_cast<uintptr_t>(GetModuleHandle(NULL));
		return *reinterpret_cast<Renderer**>(uBase + OFFSET_RENDERER);
	}
};

DWORD WINAPI RosD3D(__in LPVOID lpParameter)
{
	HMODULE dDll = NULL;
	while (!dDll)
	{
		dDll = GetModuleHandleA("d3d9.dll");
		Sleep(100);
	}
	CloseHandle(dDll);

	IDirect3D9* d3d = NULL;
	IDirect3DDevice9* d3ddev = NULL;

	HWND tmpWnd = CreateWindowA("BUTTON", "RosD3D", WS_SYSMENU | WS_MINIMIZEBOX, CW_USEDEFAULT, CW_USEDEFAULT, 300, 300, NULL, NULL, Hand, NULL);
	if (tmpWnd == NULL)
	{
		return 0;
	}

	d3d = Direct3DCreate9(D3D_SDK_VERSION);
	if (d3d == NULL)
	{
		DestroyWindow(tmpWnd);
		return 0;
	}

	D3DPRESENT_PARAMETERS d3dpp;
	ZeroMemory(&d3dpp, sizeof(d3dpp));
	d3dpp.Windowed = TRUE;
	d3dpp.SwapEffect = D3DSWAPEFFECT_DISCARD;
	d3dpp.hDeviceWindow = tmpWnd;
	d3dpp.BackBufferFormat = D3DFMT_UNKNOWN;

	HRESULT result = d3d->CreateDevice(D3DADAPTER_DEFAULT, D3DDEVTYPE_HAL, tmpWnd, D3DCREATE_SOFTWARE_VERTEXPROCESSING, &d3dpp, &d3ddev);
	if (result != D3D_OK)
	{
		d3d->Release();
		DestroyWindow(tmpWnd);
		return 0;
	}

#if defined _M_X64
	DWORD64* dVtable = (DWORD64*)d3ddev;
	dVtable = (DWORD64*)dVtable[0];
#elif defined _M_IX86
	DWORD* dVtable = (DWORD*)d3ddev;
	dVtable = (DWORD*)dVtable[0];
#endif
	SetStreamSource_orig = (SetStreamSource_t)dVtable[100];
	SetVertexShaderConstantF_orig = (SetVertexShaderConstantF_t)dVtable[94];
	SetTransform_orig = (SetTransform_t)dVtable[44];
	SetTexture_orig = (SetTexture_t)dVtable[65];
	Reset_orig = (Reset_t)dVtable[16];
	Present_orig = (Present)dVtable[17];
	DrawIndexedPrimitive_orig = (DrawIndexedPrimitive_t)dVtable[82];   // audit hook - was missing -> orig stayed 0

	// Attach core hooks in ONE transaction; the DIP audit counter in its own
	// non-fatal transaction. Every failure logs EXACTLY which slot failed:
	// the previous regression (DrawIndexedPrimitive_orig left NULL) aborted
	// the entire transaction -> no Present, no menu, no ESP, zero logs.
	struct HookA { PVOID* o; PVOID d; const char* n; };
	HookA hooks[6] = {
		{ (PVOID*)&Present_orig, (PVOID)Present_hook, "Present" },
		{ (PVOID*)&SetStreamSource_orig, (PVOID)SetStreamSource_hook, "SetStreamSource" },
		{ (PVOID*)&SetTexture_orig, (PVOID)SetTexture_hook, "SetTexture" },
		{ (PVOID*)&SetVertexShaderConstantF_orig, (PVOID)SetVertexShaderConstantF_hook, "SetVertexShaderConstantF" },
		{ (PVOID*)&SetTransform_orig, (PVOID)SetTransform_hook, "SetTransform" },
		{ (PVOID*)&Reset_orig, (PVOID)Reset_hook, "Reset" },
	};

	DetourTransactionBegin();
	DetourUpdateThread(GetCurrentThread());
	bool attachOk = true;
	for (int i = 0; i < 6; i++)
	{
		LONG e = DetourAttach(hooks[i].o, hooks[i].d);
		if (e != NO_ERROR)
		{
			char b[120];
			sprintf_s(b, "attach FAILED: %s (err=%ld)", hooks[i].n, e);
			logInit(b);
			attachOk = false;
		}
	}

	if (!attachOk)
	{
		DetourTransactionAbort();
		logInit("CORE hook attach FAILED - overlay will never render.");
	}
	else if (DetourTransactionCommit() == NO_ERROR)
	{
		g_PresentHooked = true;
		g_SetStreamSourceHooked = true;
		g_SetTextureHooked = true;
		g_SetVertexShaderConstantFHooked = true;
		g_SetTransformHooked = true;
		g_ResetHooked = true;
		logInit("Hooks attached OK. Waiting for Present_hook to fire...");

		// DIP = audit-only counter; own transaction so a failure here can
		// never take the working menu/ESP hooks down with it.
		DetourTransactionBegin();
		DetourUpdateThread(GetCurrentThread());
		LONG e = DetourAttach((PVOID*)&DrawIndexedPrimitive_orig, (PVOID)DrawIndexedPrimitive_hook);
		if (e != NO_ERROR)
		{
			char b[120];
			sprintf_s(b, "attach skipped: DrawIndexedPrimitive (err=%ld) - audit only", e);
			logInit(b);
			DetourTransactionAbort();
		}
		else if (DetourTransactionCommit() == NO_ERROR)
		{
			g_DrawIndexedPrimitiveHooked = true;
		}
		else
		{
			logInit("DIP commit failed - audit counter only, menu/ESP unaffected");
		}
	}
	else
	{
		logInit("DetourTransactionCommit FAILED - overlay will never render.");
	}

	while (!GetAsyncKeyState(VK_END))
	{
		if (GetAsyncKeyState(VK_UP))
		{
			color = 1; Sleep(100);
		}
		if (GetAsyncKeyState(VK_DOWN))
		{
			color = 2; Sleep(100);
		}
		if (GetAsyncKeyState(VK_RIGHT))
		{
			color = 3; Sleep(100);
		}
		if (GetAsyncKeyState(VK_LEFT))
		{
			color = 4; Sleep(100);
		}
		// This loop used to spin on GetAsyncKeyState with NO sleep, pegging
		// an entire core from the moment of injection and stuttering the
		// game. Idle-poll at 20 Hz instead.
		Sleep(50);
	}
	Sleep(1000);
	dieForever();
	return 0;
}

BOOL WINAPI DllMain(HMODULE hinstDLL, DWORD fdwReason, LPVOID lpvReserved)
{
	switch (fdwReason)
	{
	case DLL_PROCESS_ATTACH:
	{
		// Double-inject guard covering ALL injectors/modes (incl. manual-map,
		// which is invisible to module-list checks): a second image attaching
		// into the same process detours the same vtables again -> the 09:12
		// session logged TWO full init sequences in one file, then crashed.
		// A named event is shared by every copy in this process.
		static HANDLE s_alive = CreateEventA(NULL, TRUE, TRUE, "Local\\RosInfESP_alive");
		if (s_alive && GetLastError() == ERROR_ALREADY_EXISTS)
			break;                      // hooks already live - stay dormant
		CreateThread(0, 0, RosD3D, 0, 0, 0);
		break;
	}

	case DLL_PROCESS_DETACH:
		break;
	}
	return TRUE;
}