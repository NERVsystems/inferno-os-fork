/*
 * SDL3 GUI Backend for Inferno
 *
 * This module provides cross-platform GUI via SDL3.
 * It is completely self-contained and can be removed
 * without impacting Inferno core.
 *
 * Platforms: macOS (Metal), Linux (Vulkan/OpenGL), Windows (D3D12)
 *
 * Function signatures match stubs-headless.c for drop-in replacement.
 */

#include "dat.h"
#include "fns.h"
#include "error.h"
#include "keyboard.h"
#include <draw.h>
#include <memdraw.h>
#include <cursor.h>

#include <SDL3/SDL.h>

/* External keyboard queue (from devcons.c) */
extern Queue *gkbdq;

/* SDL3 state - private to this module */
static SDL_Window *sdl_window = NULL;
static SDL_Renderer *sdl_renderer = NULL;
static SDL_Texture *sdl_texture = NULL;
static int sdl_width = 0;
static int sdl_height = 0;
static int sdl_running = 0;

/* Mouse state */
static int mouse_x = 0;
static int mouse_y = 0;
static int mouse_buttons = 0;

/* Screen data pointer (set by attachscreen) */
static uchar *screen_data = NULL;

/*
 * Initialize SDL3 and create window
 * Returns pointer to screen buffer
 */
uchar*
attachscreen(Rectangle *r, ulong *chan, int *d, int *width, int *softscreen)
{
	if (SDL_Init(SDL_INIT_VIDEO | SDL_INIT_EVENTS) < 0) {
		fprint(2, "SDL_Init failed: %s\n", SDL_GetError());
		return nil;
	}

	/* Get screen dimensions from globals */
	sdl_width = Xsize;
	sdl_height = Ysize;

	/* Create window */
	sdl_window = SDL_CreateWindow(
		"Inferno",
		sdl_width, sdl_height,
		SDL_WINDOW_RESIZABLE
	);

	if (!sdl_window) {
		fprint(2, "SDL_CreateWindow failed: %s\n", SDL_GetError());
		SDL_Quit();
		return nil;
	}

	/* Create GPU renderer */
	sdl_renderer = SDL_CreateRenderer(sdl_window, NULL);
	if (!sdl_renderer) {
		fprint(2, "SDL_CreateRenderer failed: %s\n", SDL_GetError());
		SDL_DestroyWindow(sdl_window);
		SDL_Quit();
		return nil;
	}

	/* Enable high-DPI (Retina) support */
	float scale = SDL_GetWindowDisplayScale(sdl_window);
	if (scale > 1.0f) {
		SDL_SetRenderScale(sdl_renderer, scale, scale);
	}

	/* Create streaming texture for pixel buffer */
	sdl_texture = SDL_CreateTexture(
		sdl_renderer,
		SDL_PIXELFORMAT_ARGB8888,
		SDL_TEXTUREACCESS_STREAMING,
		sdl_width, sdl_height
	);

	if (!sdl_texture) {
		fprint(2, "SDL_CreateTexture failed: %s\n", SDL_GetError());
		SDL_DestroyRenderer(sdl_renderer);
		SDL_DestroyWindow(sdl_window);
		SDL_Quit();
		return nil;
	}

	SDL_ShowWindow(sdl_window);
	sdl_running = 1;

	/* Allocate screen buffer */
	screen_data = malloc(sdl_width * sdl_height * 4);
	if (!screen_data) {
		fprint(2, "Failed to allocate screen buffer\n");
		SDL_DestroyTexture(sdl_texture);
		SDL_DestroyRenderer(sdl_renderer);
		SDL_DestroyWindow(sdl_window);
		SDL_Quit();
		return nil;
	}

	/* Initialize to black */
	memset(screen_data, 0, sdl_width * sdl_height * 4);

	/* Return screen parameters */
	*r = Rect(0, 0, sdl_width, sdl_height);
	*chan = XRGB32;  /* 32-bit color */
	*d = 32;
	*width = sdl_width * 4;  /* bytes per row */
	*softscreen = 1;         /* software framebuffer */

	return screen_data;
}

/*
 * Flush dirty rectangle to screen
 */
void
flushmemscreen(Rectangle r)
{
	/* TODO: Use r for partial updates instead of flushing entire screen */

	if (!sdl_running || !screen_data)
		return;

	/* Upload pixel data to GPU texture */
	SDL_UpdateTexture(
		sdl_texture,
		NULL,  /* update entire texture */
		screen_data,
		sdl_width * 4  /* pitch (bytes per row) */
	);

	/* Render texture to window */
	SDL_RenderClear(sdl_renderer);
	SDL_RenderTexture(sdl_renderer, sdl_texture, NULL, NULL);
	SDL_RenderPresent(sdl_renderer);
}

/*
 * Process SDL events and generate Inferno input events
 * Called periodically from main event loop
 */
void
sdl_pollevents(void)
{
	SDL_Event event;

	if (!sdl_running)
		return;

	while (SDL_PollEvent(&event)) {
		switch (event.type) {
		case SDL_EVENT_QUIT:
			cleanexit(0);
			break;

		case SDL_EVENT_MOUSE_MOTION:
			mouse_x = (int)event.motion.x;
			mouse_y = (int)event.motion.y;
			/* Get current button state */
			mouse_buttons = 0;
			if (SDL_GetMouseState(NULL, NULL) & SDL_BUTTON_LMASK)
				mouse_buttons |= 1;
			if (SDL_GetMouseState(NULL, NULL) & SDL_BUTTON_MMASK)
				mouse_buttons |= 2;
			if (SDL_GetMouseState(NULL, NULL) & SDL_BUTTON_RMASK)
				mouse_buttons |= 4;

			mousetrack(mouse_buttons, mouse_x, mouse_y, 0);
			break;

		case SDL_EVENT_MOUSE_BUTTON_DOWN:
		case SDL_EVENT_MOUSE_BUTTON_UP:
			mouse_x = (int)event.button.x;
			mouse_y = (int)event.button.y;

			/* Update button state */
			mouse_buttons = 0;
			if (SDL_GetMouseState(NULL, NULL) & SDL_BUTTON_LMASK)
				mouse_buttons |= 1;
			if (SDL_GetMouseState(NULL, NULL) & SDL_BUTTON_MMASK)
				mouse_buttons |= 2;
			if (SDL_GetMouseState(NULL, NULL) & SDL_BUTTON_RMASK)
				mouse_buttons |= 4;

			mousetrack(mouse_buttons, mouse_x, mouse_y, 0);
			break;

		case SDL_EVENT_MOUSE_WHEEL:
			/* Scroll wheel as buttons 4 & 5 */
			if (event.wheel.y > 0)
				mouse_buttons = 8;   /* scroll up */
			else if (event.wheel.y < 0)
				mouse_buttons = 16;  /* scroll down */
			mousetrack(mouse_buttons, mouse_x, mouse_y, 0);
			mouse_buttons = 0;  /* Release scroll button */
			break;

		case SDL_EVENT_KEY_DOWN:
			{
				int key = 0;

				/* Map SDL scancodes to Inferno keys */
				switch (event.key.scancode) {
				case SDL_SCANCODE_ESCAPE:   key = 27; break;
				case SDL_SCANCODE_RETURN:   key = '\n'; break;
				case SDL_SCANCODE_KP_ENTER: key = '\n'; break;
				case SDL_SCANCODE_TAB:      key = '\t'; break;
				case SDL_SCANCODE_BACKSPACE: key = '\b'; break;
				case SDL_SCANCODE_DELETE:   key = 0x7F; break;
				case SDL_SCANCODE_UP:       key = Up; break;
				case SDL_SCANCODE_DOWN:     key = Down; break;
				case SDL_SCANCODE_LEFT:     key = Left; break;
				case SDL_SCANCODE_RIGHT:    key = Right; break;
				case SDL_SCANCODE_HOME:     key = Home; break;
				case SDL_SCANCODE_END:      key = End; break;
				case SDL_SCANCODE_PAGEUP:   key = Pgup; break;
				case SDL_SCANCODE_PAGEDOWN: key = Pgdown; break;
				case SDL_SCANCODE_INSERT:   key = Ins; break;
				case SDL_SCANCODE_F1:       key = KF|1; break;
				case SDL_SCANCODE_F2:       key = KF|2; break;
				case SDL_SCANCODE_F3:       key = KF|3; break;
				case SDL_SCANCODE_F4:       key = KF|4; break;
				case SDL_SCANCODE_F5:       key = KF|5; break;
				case SDL_SCANCODE_F6:       key = KF|6; break;
				case SDL_SCANCODE_F7:       key = KF|7; break;
				case SDL_SCANCODE_F8:       key = KF|8; break;
				case SDL_SCANCODE_F9:       key = KF|9; break;
				case SDL_SCANCODE_F10:      key = KF|10; break;
				case SDL_SCANCODE_F11:      key = KF|11; break;
				case SDL_SCANCODE_F12:      key = KF|12; break;
				default:
					/* Use key code for printable characters */
					if (event.key.key >= 32 && event.key.key < 127)
						key = event.key.key;
					break;
				}

				if (key != 0)
					gkbdputc(gkbdq, key);
			}
			break;

		case SDL_EVENT_WINDOW_RESIZED:
			sdl_width = event.window.data1;
			sdl_height = event.window.data2;

			/* Recreate texture at new size */
			if (sdl_texture)
				SDL_DestroyTexture(sdl_texture);

			sdl_texture = SDL_CreateTexture(
				sdl_renderer,
				SDL_PIXELFORMAT_ARGB8888,
				SDL_TEXTUREACCESS_STREAMING,
				sdl_width, sdl_height
			);

			/* Reallocate screen buffer */
			if (screen_data)
				free(screen_data);
			screen_data = malloc(sdl_width * sdl_height * 4);
			if (screen_data)
				memset(screen_data, 0, sdl_width * sdl_height * 4);

			/* TODO: Notify Inferno of resize */
			break;
		}
	}
}

/*
 * Set mouse pointer position
 */
void
setpointer(int x, int y)
{
	if (!sdl_running)
		return;

	SDL_WarpMouseInWindow(sdl_window, (float)x, (float)y);
	mouse_x = x;
	mouse_y = y;
}

/*
 * Draw cursor (Inferno's software cursor)
 */
void
drawcursor(Drawcursor *c)
{
	/* SDL3 handles the cursor - we can implement custom cursor here if needed */
	USED(c);

	/* For now, use default cursor */
	/* TODO: Convert Inferno cursor to SDL cursor and set it */
}

/*
 * Read clipboard/snarf buffer
 */
char*
clipread(void)
{
	if (!sdl_running)
		return nil;

	if (!SDL_HasClipboardText())
		return nil;

	char *text = SDL_GetClipboardText();
	if (!text)
		return nil;

	/* Copy to Inferno-managed memory */
	char *result = strdup(text);
	SDL_free(text);

	return result;
}

/*
 * Write to clipboard/snarf buffer
 */
int
clipwrite(char *buf)
{
	if (!sdl_running)
		return 0;

	if (SDL_SetClipboardText(buf) < 0)
		return 0;

	return strlen(buf);
}

/*
 * Shutdown SDL3
 */
void
sdl_shutdown(void)
{
	sdl_running = 0;

	if (screen_data) {
		free(screen_data);
		screen_data = NULL;
	}

	if (sdl_texture) {
		SDL_DestroyTexture(sdl_texture);
		sdl_texture = NULL;
	}

	if (sdl_renderer) {
		SDL_DestroyRenderer(sdl_renderer);
		sdl_renderer = NULL;
	}

	if (sdl_window) {
		SDL_DestroyWindow(sdl_window);
		sdl_window = NULL;
	}

	SDL_Quit();
}
