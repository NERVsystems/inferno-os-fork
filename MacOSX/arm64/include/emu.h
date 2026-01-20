/*
 * system- and machine-specific declarations for emu:
 * floating-point save and restore, signal handling primitive, and
 * implementation of the current-process variable `up'.
 *
 * arm64 macOS version
 */

extern Proc *getup(void);
#define	up	(getup())

/*
 * This structure must agree with FPsave and FPrestore asm routines
 * arm64 uses NEON/FP registers but macOS handles context switching
 * so we use a minimal stub structure
 */
typedef struct FPU FPU;
struct FPU
{
	uchar	env[32];	/* placeholder - arm64 FP state handled by OS */
};

typedef sigjmp_buf osjmpbuf;
#define	ossetjmp(buf)	sigsetjmp(buf, 1)
