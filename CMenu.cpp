#include "StandardIncludes.h"
#include "CMenu.h"
#include "CSound.h"
#include "Sounds.h"
#include <new>

//-----------------------------------------------------------------------------
// Name: PostReset()
// Desc: Creates Fonts and other Resources for Menu
//-----------------------------------------------------------------------------

void cMenu::PostReset(LPDIRECT3DDEVICE9 pDevice)
{
	if (!pDevice || font != NULL)
		return;

	CD3DFont* candidate = new (std::nothrow) CD3DFont((char*)"Tahoma", 7, D3DFONT_BOLD);
	if (!candidate)
	{
		FontCreated = false;
		return;
	}

	// Do not publish a partially initialized font. Keep reset/retry safe.
	if (FAILED(candidate->InitDeviceObjects(pDevice)) ||
		FAILED(candidate->RestoreDeviceObjects()))
	{
		delete candidate;
		FontCreated = false;
		return;
	}
	font = candidate;
	FontCreated = true;
}

//-----------------------------------------------------------------------------
// Name: PreReset()
// Desc: Releases Fonts / objects for menu
//-----------------------------------------------------------------------------

void cMenu::PreReset(void)
{
	if (!font) // may be called from Reset_hook() before PostReset ever created it
		return;

	// CD3DFont's destructor releases its device-dependent objects.
	delete font;
	font = NULL;
	this->FontCreated = false;
}

//-----------------------------------------------------------------------------
// Name: Init()
// Desc: Load Menu Defaults / Prepare Menu For Usage
//-----------------------------------------------------------------------------

void cMenu::Init()
{
	if (opt.options.reset)INIT=false;
	if(!INIT){
		opt.options.move=0;		// BUG FIX FOR RESET DISABLE MOVE BEFORE SETTING COORDINATES
		X=30;
		Y=30;
		WIDTH=176;			    // MENU WIDTH
		I_OFS=4;			    // OFSET FOR ITEM
		S_OFS=WIDTH-4;			// OFSET FOR STATE
		T_SPC=16;				// Space from Title and Start of Items
		F_SPC=16;				// Footer Spacing Hook Menu
		I_SPC=15;				// Item Spacing
		I_CUR=0;				// Set current Item
		SHOW=false;				// hidden by default - press INSERT (Ros-D3D style)
		INIT=true;				// STOP INITATION
	}
}

//-----------------------------------------------------------------------------
// Name: FPS()
// Desc: Keeps Track of Current Frames Persecond Make sure if its already called to specify a 1 as parameter
//-----------------------------------------------------------------------------

char* cMenu::FPS(int en)
{
	static int	 FPScounter = 0;
	static ULONGLONG lastTick = 0;
	static char cfps[32] = "";
	if (!en)
	{
		const ULONGLONG now = GetTickCount64();
		FPScounter++;
		if (lastTick == 0) lastTick = now;
		if (now - lastTick >= 1000)
		{
			sprintf_s(cfps, sizeof(cfps), "%d FPS", FPScounter);
			FPScounter = 0;
			lastTick = now;
		}
	}
	return cfps;
}

//-----------------------------------------------------------------------------
// Name: TIME()
// Desc: Outputs Current Time in USA Format
//-----------------------------------------------------------------------------

char* cMenu::TIME(void)
{
	static char ctime[20] = "";
	time_t current_time = time(NULL);
	struct tm current_tm = {};
	if (current_time == (time_t)-1 || localtime_s(&current_tm, &current_time) != 0)
	{
		strcpy_s(ctime, sizeof(ctime), "--:--:--");
		return ctime;
	}

	int hour = current_tm.tm_hour % 12;
	if (hour == 0) hour = 12;
	sprintf_s(ctime, sizeof(ctime), "%d:%02d:%02d %s", hour,
		current_tm.tm_min, current_tm.tm_sec, current_tm.tm_hour >= 12 ? "PM" : "AM");
	return ctime;
}

//-----------------------------------------------------------------------------
// Name: DATE()
// Desc: Outputs Current Date in USA Format
//-----------------------------------------------------------------------------

char* cMenu::DATE(void)
{
	static const char* const months[] = {
		"Jan.", "Feb.", "Mar.", "Apr.", "May", "June",
		"July", "Aug.", "Sept.", "Oct.", "Nov.", "Dec."
	};
	static char logbuf[32];
	time_t current_time = time(NULL);
	struct tm current_tm = {};
	if (current_time == (time_t)-1 || localtime_s(&current_tm, &current_time) != 0 ||
		current_tm.tm_mon < 0 || current_tm.tm_mon >= 12)
	{
		strcpy_s(logbuf, sizeof(logbuf), "---- --, ----");
		return logbuf;
	}

	sprintf_s(logbuf, sizeof(logbuf), "%s %02d, %04d", months[current_tm.tm_mon],
		current_tm.tm_mday, current_tm.tm_year + 1900);
	return logbuf;
}

//-----------------------------------------------------------------------------
// Name: oprintf()
// Desc: equiv to sprintf but for output into of dest
//-----------------------------------------------------------------------------

char* cMenu::oprintf (const char *fmt, ...)
{
	static char buffer[225] = "";
	va_list va_alist;
	va_start (va_alist, fmt);
	_vsnprintf(buffer, sizeof(buffer), fmt, va_alist);
	va_end(va_alist);
	buffer[sizeof(buffer) - 1] = '\0';
	return buffer;
}
//-----------------------------------------------------------------------------
// Name: Save()
// Desc: Saves Menu Item states for later Restoration
//-----------------------------------------------------------------------------

void cMenu::Save(char* szSection, char* szKey, int iValue,LPCSTR file)
{
	char szValue[255];
	sprintf(szValue, "%d", iValue);
	WritePrivateProfileString(szSection,  szKey, szValue, file); 
}

//-----------------------------------------------------------------------------
// Name: Load()
// Desc: Loads Menu Item States From Previously Saved File
//-----------------------------------------------------------------------------

int cMenu::Load(char* szSection, char* szKey, int iDefaultValue,LPCSTR file)
{
	int iResult = GetPrivateProfileInt(szSection,  szKey, iDefaultValue, file); 
	return iResult;
}

//-----------------------------------------------------------------------------
// Name: additem()
// Desc: BaseFunction for aitem,acat,and atext
//-----------------------------------------------------------------------------

void cMenu::additem(char *title, char *states,int type, int *var, int show, int when)
{
	if (show == when && NO >= 0 && NO < ITEM_ARRAY && title && states && var)
	{
		strncpy(items[NO].title, title, sizeof(items[NO].title) - 1);
		items[NO].title[sizeof(items[NO].title) - 1] = '\0';
		getfield(states, items[NO].state, sizeof(items[NO].state), *var + 1);
		items[NO].type = type;
		items[NO].max = nofields(states);
		items[NO].val = var;
		NO++;
	}
	if(type!=T_TEXT)
	{
		if (opt.options.load)
			*var = Load((char *)"Items", title, *var,Tools.GetDirectoryFile((char *)"settings.ini"));
		if (opt.options.save)
			Save((char *)"Items", title, *var,Tools.GetDirectoryFile((char *)"settings.ini"));
		if (opt.options.reset)
			*var=0;
	}
}

//-----------------------------------------------------------------------------
// Name: acat()
// Desc: Adds Folder/Category to Item index
//-----------------------------------------------------------------------------

void cMenu::acat(char *title, char *states,int *var)
{
	additem(title,states,T_CAT,var,0,0);
}

//-----------------------------------------------------------------------------
// Name: aitem()
// Desc: Adds regular item to Item index
//-----------------------------------------------------------------------------

void cMenu::aitem(char *title, char *states,int *var,int show,int when)
{
	additem(title,states,T_ITEM,var,show,when);
}

//-----------------------------------------------------------------------------
// Name: atext()
// Desc: Adds Text item to item index
//-----------------------------------------------------------------------------

void cMenu::atext(char *title, char *states,int show,int when)
{
	additem(title,states,T_TEXT,&opt.text,show,when);
}

void cMenu::atext(char *title, char *states)
{
	additem(title,states,T_TEXT,&opt.text,1,1);
}

//-----------------------------------------------------------------------------
// Name: nofields()
// Desc: Calculates Number of Fields in a String based on deliminator
//-----------------------------------------------------------------------------

int cMenu::nofields(const char *str)
{
	if (!str || !*str) return 0;
	int count = 1;
	for (const char *p = str; *p; ++p)
		if (*p == '|') ++count;
	return count;
}

//-----------------------------------------------------------------------------
// Name: getfield()
// Desc: Bounded field extraction for the fixed-size menu state buffer
//-----------------------------------------------------------------------------

void cMenu::getfield(const char *str, char *dst, size_t dstSize, int no)
{
	if (!dst || dstSize == 0) return;
	dst[0] = '\0';
	if (!str) return;
	if (no < 1) no = 1;

	const char *begin = str;
	for (int field = 1; field < no && *begin; ++field)
	{
		const char *delimiter = strchr(begin, '|');
		if (!delimiter) { begin += strlen(begin); break; }
		begin = delimiter + 1;
	}
	const char *end = strchr(begin, '|');
	size_t length = end ? (size_t)(end - begin) : strlen(begin);
	if (length >= dstSize) length = dstSize - 1;
	memcpy(dst, begin, length);
	dst[length] = '\0';
}

//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
// Name: DrawBox()
// Desc: Fills Rectangle using DrawPrimitive Up
//-----------------------------------------------------------------------------

void cMenu::DrawBox( int x, int y, int w, int h, D3DCOLOR Color,LPDIRECT3DDEVICE9 pDevice)
{
	if (!pDevice || w <= 0 || h <= 0) return;
	struct Vertex 
	{
		float x,y,z,ht;
		DWORD Color;
	}
	V[4] = 
	{
		{(float)x,(float)(y+h), 0.0f, 0.0f, Color},
		{(float)x,(float)y, 0.0f, 0.0f, Color},
		{(float)(x+w),(float)(y+h), 0.0f, 0.0f, Color},
		{(float)(x+w),(float)y, 0.0f, 0.0f, Color}
	};
	pDevice->SetTexture(0, NULL);
	pDevice->SetPixelShader(NULL);
	pDevice->SetFVF(D3DFVF_XYZRHW | D3DFVF_DIFFUSE); 
	pDevice->SetRenderState(D3DRS_ALPHABLENDENABLE,true);
	pDevice->SetRenderState(D3DRS_DESTBLEND,D3DBLEND_INVSRCALPHA);
	pDevice->SetRenderState(D3DRS_SRCBLEND,D3DBLEND_SRCALPHA);
	pDevice->DrawPrimitiveUP(D3DPT_TRIANGLESTRIP,2,V,sizeof(Vertex));
	return;
}

//-----------------------------------------------------------------------------
// Name: DrawBorder()
// Desc: Fills outside of Rectangle using 4 calls to DrawBox
//-----------------------------------------------------------------------------

void cMenu::DrawBorder(int x, int y, int w, int h, int s, D3DCOLOR Color, LPDIRECT3DDEVICE9 pDevice)
{
    DrawBox(x, y-1, w, s, Color, pDevice );
    DrawBox(x-1, y, s, h, Color, pDevice );
    DrawBox((x+w), y, s, h, Color, pDevice );
    DrawBox(x, (y+h), w, s, Color, pDevice );
	return;
}

//-----------------------------------------------------------------------------
// Name: DrawGameTextPixelFlag()
//-----------------------------------------------------------------------------

void cMenu::DrawGameTextPixelFlag(int x, int y, DWORD color, DWORD flags, char *szFormat, ... )
{
    if( !szFormat )return;

    char logbuf[256] = { 0 };
    if (!font) return;

    va_list va_alist;
    va_start(va_alist, szFormat);
    _vsnprintf(logbuf, sizeof(logbuf), szFormat, va_alist);
    va_end(va_alist);
    logbuf[sizeof(logbuf) - 1] = '\0';

    if( flags == DT_RIGHT )
    {
        SIZE Size = {0,0};
        if(font->GetTextExtent(logbuf, &Size) == S_OK)
        {
            x -= Size.cx;
        }
        flags = 0;
    } else if( flags == DT_CENTER )
    {
        SIZE Size = {0,0};
        if(font->GetTextExtent(logbuf, &Size) == S_OK)
        {
            x -= (Size.cx/2);
        }
        flags = 0;
    }
    font->DrawText((float)x+1, (float)y, D3DCOLOR_ARGB( 255, 0, 0, 0 ), logbuf, flags);
    font->DrawText((float)x-1, (float)y, D3DCOLOR_ARGB( 255, 0, 0, 0 ), logbuf, flags);
    font->DrawText((float)x, (float)y+1, D3DCOLOR_ARGB( 255, 0, 0, 0 ), logbuf, flags);
    font->DrawText((float)x, (float)y-1, D3DCOLOR_ARGB( 255, 0, 0, 0 ), logbuf, flags);
    font->DrawText((float)x, (float)y, color, logbuf, flags);
}

//-----------------------------------------------------------------------------
// Name: ShowMenu()
// Desc: Core Menu Function Displays Menu Calls Other Menu functions and navigation
//-----------------------------------------------------------------------------

void cMenu::ShowMenu(LPDIRECT3DDEVICE9 pDevice)
{
	if (!pDevice) return;
	//-----------------------------------------------------------------------------
	// Desc: Check Hotkeys
	// Level-based reads (0x8000 = current physical state) + our own
	// prev-state latch: the &1 edge bit is consumed by ros64's own key
	// polling before Present runs, so edge reads here never fired.
	static bool pLm = false, pRm = false;
	bool bLm = (GetAsyncKeyState(VK_LBUTTON) & 0x8000) != 0;
	bool bRm = (GetAsyncKeyState(VK_RBUTTON) & 0x8000) != 0;
	//-----------------------------------------------------------------------------
	int	lm		=	(bLm && !pLm) ? 1 : 0;
	int	rm		=	(bRm && !pRm) ? 1 : 0;
	pLm = bLm; pRm = bRm;
	// Arrow keys: level-based, per-key latch (see below).
	int left = 0, right = 0, up = 0, down = 0;
	{
		// Level-based + per-key latch (same reason as lm/rm above).
		// fresh = fire once on a new press; hold-repeat after 500 ms @ 150 ms.
		static bool  pB[4] = {};
		static bool  fresh[4] = {};
		static ULONGLONG pressAt[4] = {};
		static ULONGLONG fireAt[4] = {};
		ULONGLONG now = GetTickCount64();
		bool b[4] = {
			(GetAsyncKeyState(VK_LEFT)  & 0x8000) != 0,
			(GetAsyncKeyState(VK_RIGHT) & 0x8000) != 0,
			(GetAsyncKeyState(VK_UP)    & 0x8000) != 0,
			(GetAsyncKeyState(VK_DOWN)  & 0x8000) != 0 };
		int* out[4] = { &left, &right, &up, &down };
		for (int k = 0; k < 4; k++)
		{
			if (b[k] && !pB[k]) { pressAt[k] = now; fresh[k] = true; }
			pB[k] = b[k];
			if (!b[k]) continue;
			bool fire = fresh[k];
			if (!fire && now - pressAt[k] > 500 && now - fireAt[k] >= 150) fire = true;
			if (fire) { *out[k] = 1; fireAt[k] = now; fresh[k] = false; }
		}
	}
	//-----------------------------------------------------------------------------
	// Desc: Prepare/Reset Menu
	//-----------------------------------------------------------------------------

	Init();

	//-----------------------------------------------------------------------------
	// Desc: Show The Menu
	//-----------------------------------------------------------------------------
	{
		// Level-based INSERT with own latch - edge &1 was consumed by the
		// game before Present ran, so SHOW never toggled. Fire on fresh
		// press (down-transition), 150 ms debounce.
		static bool pIns = false;
		static ULONGLONG lastInsert = 0;
		ULONGLONG now = GetTickCount64();
		bool bIns = (GetAsyncKeyState(VK_INSERT) & 0x8000) != 0;
		if (bIns && !pIns && now - lastInsert > 150)
		{
			lastInsert = now;
			SHOW = (!SHOW);
		}
		pIns = bIns;
	}
	if(SHOW){

		//-----------------------------------------------------------------------------
		// Desc: Get Mouse Coordinates and translate
		//-----------------------------------------------------------------------------
		
		//-----------------------------------------------------------------------------
		// Desc: Move Menu
		//-----------------------------------------------------------------------------

		GetCursorPos(&mpos);// Update Mouse Coordinates
		ScreenToClient(GetForegroundWindow(),&mpos); // Translate to Current Window

		if(opt.options.move && GetAsyncKeyState(VK_RCONTROL))	// If Options for Left Control is Set
		{
			X =(((X<=mpos.x+4) && (X>=mpos.x)) || ((X>=mpos.x-4) && (X<=mpos.x)))?(X=mpos.x):(X+=((mpos.x-X)/4));
			Y =(((Y<=mpos.y+4) && (Y>=mpos.y)) || ((Y>=mpos.y-4) && (Y<=mpos.y)))?(Y=mpos.y):(Y+=((mpos.y-Y)/4));
		}
		//-----------------------------------------------------------------------------
		// Desc: Draw Menu Header
		//-----------------------------------------------------------------------------
		DrawBox(X,Y+3,WIDTH,T_SPC,C_BOX2,pDevice);// Render Menu Header Backround
		DrawBorder(X,Y+3,WIDTH,T_SPC,1,C_BORDER,pDevice);// set-up border
    	DrawGameTextPixelFlag(MC_FCTR(X,MC_MAXX),Y+5,C_TITLE,DT_CENTER|DT_SHADOW, (char *)"~|| ROS Infinity v1 ||~");
         
		//-----------------------------------------------------------------------------
		// Desc: Fill Item Array and Render Menu Border and Box
		//-----------------------------------------------------------------------------

		DrawBox(X,MC_MSY,WIDTH,(NO*I_SPC),C_BOX,pDevice);// Render Menu Backround for items
		DrawBorder(X,MC_MSY,WIDTH,(NO*I_SPC),1,C_BORDER,pDevice);// set-up border

		//Draw Left Box
		DrawBox(X-10,MC_MSY,5,(NO*I_SPC)+42,C_BOX2,pDevice);
		DrawBorder(X-10,MC_MSY,5,(NO*I_SPC)+42,1,C_BORDER,pDevice);

		//Draw Right Box
		DrawBox(X+WIDTH+5,MC_MSY,5,(NO*I_SPC)+42,C_BOX2,pDevice);
		DrawBorder(X+WIDTH+5,MC_MSY,5,(NO*I_SPC)+42,1,C_BORDER,pDevice);

		NO=0;
		acat((char *)"Main Options", (char *)"Show|Hide",&opt.d3d.main);
			aitem((char *)"CrossHair", (char *)"OFF|ON",&opt.d3d.cross,opt.d3d.main,1);
			aitem((char *)"ESP", (char *)"OFF|ON",&opt.d3d.esp,opt.d3d.main,1);
			aitem((char *)"Chams", (char *)"OFF|ON",&opt.d3d.Chams,opt.d3d.main,1);
			aitem((char *)"Aimbot", (char *)"OFF|ON", &opt.d3d.aimbot, opt.d3d.main, 1);
		aitem((char *)"Fast Drop", (char *)"OFF|ON", &opt.d3d.fastdrop, opt.d3d.main, 1);
		aitem((char *)"No Recoil", (char *)"OFF|ON", &opt.d3d.norecoil, opt.d3d.main, 1);


		acat((char *)"Chams Opions", (char *)"Show|Hide", &opt.chamsopt.main);
			aitem((char *)"Red", (char *)"OFF|ON", &opt.chamsopt.red, opt.chamsopt.main, 1);
			aitem((char *)"Green", (char *)"OFF|ON", &opt.chamsopt.green, opt.chamsopt.main, 1);
			aitem((char *)"Blue", (char *)"OFF|ON", &opt.chamsopt.blue, opt.chamsopt.main, 1);
			aitem((char *)"Alpha", (char *)"OFF|ON", &opt.chamsopt.alpha, opt.chamsopt.main, 1);


		acat((char *)"ESP Opions", (char *)"Show|Hide", &opt.espopt.main);
			aitem((char *)"Distance", (char *)"OFF|ON", &opt.espopt.dist, opt.espopt.main, 1);
			aitem((char *)"2D Boxes ", (char *)"OFF|ON", &opt.espopt.box2, opt.espopt.main, 1);
			aitem((char *)"3D Boxes", (char *)"OFF|ON", &opt.espopt.box3, opt.espopt.main, 1);
			aitem((char *)"Lines", (char *)"OFF|ON", &opt.espopt.lines, opt.espopt.main, 1);
			aitem((char *)"Unknown Entity Type", (char *)"OFF|ON", &opt.espopt.type, opt.espopt.main, 1);
			aitem((char *)"Player Health", (char *)"OFF|ON", &opt.espopt.health, opt.espopt.main, 1);
			aitem((char *)"Item ESP", (char *)"OFF|ON", &opt.espopt.item, opt.espopt.main, 1);
			aitem((char *)"Player ESP", (char *)"OFF|ON", &opt.espopt.player, opt.espopt.main, 1);
			aitem((char *)"Vehicle ESP", (char *)"OFF|ON", &opt.espopt.vehicle, opt.espopt.main, 1);


		acat((char *)"OPTIONS", (char *)"Show|Hide",&opt.options.main);
			aitem((char *)"Move Menu", (char *)"OFF|R-Ctrl",&opt.options.move,opt.options.main,1);
			aitem((char *)"Save Setting", (char *)"OFF|Saving",&opt.options.save,opt.options.main,1);
			aitem((char *)"Load Setting", (char *)"OFF|Loading",&opt.options.load,opt.options.main,1);
			aitem((char *)"Exit Cheat", (char *)"OFF|Exiting..",&opt.options.reset,opt.options.main,1);

		opt.options.save=0;
		opt.options.load=0;

		//-----------------------------------------------------------------------------
		// Desc: Loop Threw Item Index and Render Items
		//-----------------------------------------------------------------------------

		for(int no=0; no<NO; no++)
		{
			D3DCOLOR text;
			D3DCOLOR text2;
			D3DCOLOR text3;

			text=(*(items[no].val)>0)?C_ON:C_OFF;
			text2=(*(items[no].val)>0)?C_ON2:C_OFF2;
			text3=(*(items[no].val)>0)?C_ON2:C_OFF3;

			if(items[no].type==T_CAT)
				text=C_CAT;

			if(I_CUR==no){
				DrawBox(X,MC_ITEMY(no),WIDTH,I_SPC,C_CUR,pDevice);
			}

			if(mpos.x>X && mpos.x<MC_MAXX && mpos.y>MC_ITEMY(no) && mpos.y<MC_ITEMY(no)+I_SPC){
				DrawBox(X,MC_ITEMY(no),WIDTH,I_SPC,C_CUR,pDevice);
			}

			if(items[no].type!=T_CAT){
				DrawBox(X+5, MC_ITEMY(no)+5, 5, 5, text3, pDevice);
				DrawBorder(X+5, MC_ITEMY(no)+5, 5, 5,1, C_BORDER,pDevice);
			}

			if(items[no].type==T_CAT){
				text2=C_CAT;
				DrawGameTextPixelFlag(X+I_OFS,MC_ITEMY(no)+2,text,DT_SHADOW,items[no].title);
			}
			else{
				DrawGameTextPixelFlag(X+I_OFS+12,MC_ITEMY(no)+2,text,DT_SHADOW,items[no].title);
			}
			DrawGameTextPixelFlag(X+S_OFS,MC_ITEMY(no)+2,text2,DT_RIGHT|DT_SHADOW,items[no].state);
		}

		//-----------------------------------------------------------------------------
		// Desc: Draw Info and FrameRate()
		//-----------------------------------------------------------------------------

		// Draw Info
		DrawBox(X,MC_ITEMY1(NO)+(F_SPC/2)-2,WIDTH/2,(F_SPC),C_BOX,pDevice);
		DrawBorder(X,MC_ITEMY1(NO)+(F_SPC/2)-2,WIDTH/2,(F_SPC),1,C_BORDER,pDevice);
		DrawGameTextPixelFlag(X+(WIDTH)/4,MC_ITEMY1(NO)+(F_SPC/2)+1,C_INFO,DT_CENTER|DT_SHADOW,(char *)"By Ashesh");
		// Draw FrameRate
		DrawBox(X+(WIDTH)/2,MC_ITEMY1(NO)+(F_SPC/2)-2,WIDTH/2,(F_SPC),C_BOX,pDevice);
		DrawBorder(X+(WIDTH)/2,MC_ITEMY1(NO)+(F_SPC/2)-2,WIDTH/2,(F_SPC),1,C_BORDER,pDevice);
		DrawGameTextPixelFlag(X+((WIDTH)/4)*3,MC_ITEMY1(NO)+(F_SPC/2)+1,C_INFO,DT_CENTER|DT_SHADOW,FPS(0));

		//-----------------------------------------------------------------------------
		// Desc: Draw Menu Date and Time()
		//-----------------------------------------------------------------------------

		// Draw Date
		DrawBox(X,MC_ITEMY2(NO)+(F_SPC/2)-2,WIDTH/2,(F_SPC),C_BOX,pDevice);
		DrawBorder(X,MC_ITEMY2(NO)+(F_SPC/2)-2,WIDTH/2,(F_SPC),1,C_BORDER,pDevice);
		DrawGameTextPixelFlag(X+(WIDTH)/4,MC_ITEMY2(NO)+(F_SPC/2)+1,C_INFO2,DT_CENTER|DT_SHADOW,DATE());
		// Draw Time
		DrawBox(X+(WIDTH)/2,MC_ITEMY2(NO)+(F_SPC/2)-2,WIDTH/2,(F_SPC),C_BOX,pDevice);
		DrawBorder(X+(WIDTH)/2,MC_ITEMY2(NO)+(F_SPC/2)-2,WIDTH/2,(F_SPC),1,C_BORDER,pDevice);
		DrawGameTextPixelFlag(X+((WIDTH)/4)*3,MC_ITEMY2(NO)+(F_SPC/2)+1,C_INFO2,DT_CENTER|DT_SHADOW,TIME());

		//-----------------------------------------------------------------------------
		// Desc: Draw Menu Footer()
		//-----------------------------------------------------------------------------

		DrawBox(X,MC_ITEMY3(NO)+(F_SPC/2)-2,WIDTH,(F_SPC),C_BOX2,pDevice);// Draw Footer Filled
		DrawBorder(X,MC_ITEMY3(NO)+(F_SPC/2)-2,WIDTH,(F_SPC),1,C_BORDER,pDevice);// Footer Border
		DrawGameTextPixelFlag(MC_FCTR(X,MC_MAXX),MC_ITEMY3(NO)+(F_SPC/2),C_FOOTER,DT_CENTER|DT_SHADOW, (char *)".....");

		//-----------------------------------------------------------------------------
		// Desc: Mouse Navigation
		//-----------------------------------------------------------------------------

		int mno = 999; // Item Mouse is on

		if(mpos.x>X && mpos.x<MC_MAXX && mpos.y<MC_ITEMY(NO) && mpos.y>Y)
			mno = ((mpos.y-T_SPC)>Y)?((mpos.y - Y - T_SPC - (T_SPC/2)) / I_SPC):(999);

		if (mno >= 0 && mno < NO && items[mno].val && rm && (*items[mno].val) > 0)
		{
			(*items[mno].val)-=1;
			Sound.wav.playsoundmem((LPCSTR)SWITCH);
		}

		if (mno >= 0 && mno < NO && items[mno].val && lm && items[mno].max > 0)
		{
			// Wrap to OFF instead of stopping at max-1. With the old bound a
			// second left-click did nothing once a feature was ON, which is
			// exactly "I can turn features on but never turn them off".
			(*items[mno].val) = ((*items[mno].val) + 1 >= items[mno].max) ? 0 : (*items[mno].val) + 1;
			Sound.wav.playsoundmem((LPCSTR)SWITCH);
		}

		//-----------------------------------------------------------------------------
		// Desc: Keyboard Navigation()
		//-----------------------------------------------------------------------------

		if(NO > 0)
		{
			// Items are re-built every frame; after a category hides, the old
			// cursor index can point past the new list (stale item state).
			if(I_CUR >= NO) I_CUR = NO - 1;

			if (items[I_CUR].val && left && (*items[I_CUR].val) > 0)
			{
				(*items[I_CUR].val)-=1;
				Sound.wav.playsoundmem((LPCSTR)SWITCH);
			}

			if (items[I_CUR].val && right && items[I_CUR].max > 0)
			{
				// Wrap to OFF - same rationale as the left-click path above.
				(*items[I_CUR].val) = ((*items[I_CUR].val) + 1 >= items[I_CUR].max) ? 0 : (*items[I_CUR].val) + 1;
				Sound.wav.playsoundmem((LPCSTR)SWITCH);
			}

			if (up || down || items[I_CUR].type == T_TEXT)
			{
				// The list can contain only text rows when conditional items
				// are hidden. Bound the search so navigation cannot spin forever.
				bool foundSelectable = false;
				for (int step = 0; step < NO; ++step)
				{
					if (up)
						I_CUR = (I_CUR == 0) ? (NO - 1) : (I_CUR - 1);
					else
						I_CUR = (I_CUR + 1) % NO;
					if (items[I_CUR].type != T_TEXT && items[I_CUR].val)
					{
						foundSelectable = true;
						break;
					}
				}
				if (foundSelectable)
					Sound.wav.playsoundmem((LPCSTR)MOVE);
			}
		}

		//-----------------------------------------------------------------------------
		// Desc: Menu Saftey / Sanity Checks and ReEncryption
		//-----------------------------------------------------------------------------

		if(NO>0 && I_CUR>=NO)I_CUR=NO-1; // Prevent Selection From Hiding be hind hidden item

		//-----------------------------------------------------------------------------

		//Draw a Cursor; Full credits to Credzis
		Tools.DrawMouse(D3DXVECTOR2((float)mpos.x,(float)mpos.y),D3DCOLOR_RGBA(0,255,0,255));
		//-----------------------------------------------------------------------------
	}
}