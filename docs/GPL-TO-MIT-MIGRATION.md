# GPL-to-MIT Migration Plan for Infernode

**Goal:** Replace GPL/LGPL components from acme-sac with MIT-licensed components from canonical inferno-os, while preserving all custom infernode enhancements.

**Status:** Planning Phase
**Author:** Migration plan created 2026-01-20
**Timeline:** TBD based on testing requirements

---

## Executive Summary

Infernode is currently based on acme-sac, which has mixed GPL/LGPL/MIT licensing. The canonical inferno-os repository has been re-licensed under MIT. This migration will replace all GPL/LGPL components with MIT equivalents while preserving infernode's unique 64-bit support, formal verification, JIT improvements, and NERV-specific features.

---

## Current License Status (GPL/LGPL Contamination)

### GPL Components (Must Replace)
- **appl/** directory - All applications (GPL per NOTICE file)
  - appl/acme/ - Acme editor
  - appl/charon/ - Web browser
  - appl/wm/ - Window manager applications
  - appl/cmd/ - Command-line utilities
  - appl/lib/ - Limbo libraries
  - **EXCEPTION:** appl/nerv/ is custom NERV work (keep)

### LGPL Components (Must Replace)
- **libinterp/** - Virtual machine library (LGPL per NOTICE file)
- **module/** - Limbo module interfaces (LGPL per NOTICE file)

### MIT/Liberal Components (Can Keep)
- **emu/** - Emulator kernels (MIT-style "free for all")
- **lib9/, libbio/, libdraw/, etc.** - Core C libraries (MIT-style)
- **limbo/** - Limbo compiler (no NOTICE file, likely GPL but easy to replace)

---

## Custom Infernode Modifications to PRESERVE

### 1. 64-Bit Architecture Support (CRITICAL)
**Location:** Throughout codebase
**Description:**
- WORD=intptr (8 bytes on 64-bit)
- IBY2WD=sizeof(void*) (8 bytes)
- Module header generation for 64-bit
- Auto-generated headers: sysmod.h, loadermod.h, drawmod.h, etc.

**Files with 64-bit changes:**
- All mkfiles with WORD/IBY2WD definitions
- libinterp/*mod.h (auto-generated, must regenerate)
- emu/*/srvm.h (auto-generated, platform-specific)
- Throughout C code: pointer arithmetic, structure sizes

**Commits:** ~50+ commits from pdfinn related to 64-bit porting

### 2. ARM64 JIT Implementation (CRITICAL)
**Location:** emu/Linux/, emu/MacOSX/
**Description:**
- Working ARM64 JIT compiler using caller-saved registers (X9-X12)
- Literal pool implementation for AXIMM storage
- Extensive debugging and fixes for ARM64-specific issues

**Key Files:**
- emu/*/arm64.c (if exists)
- JIT-related code in emulator

**Commits:** 30+ commits from pdfinn on JIT work
**Documentation:** ARM64-JIT-BREAKTHROUGH-SESSION.md, SOLUTION-LITERAL-POOL.md

### 3. Formal Verification Framework (UNIQUE)
**Location:** formal-verification/
**Description:** Complete formal verification of namespace isolation
- TLA+ models
- SPIN models
- CBMC C verification
- Frama-C/ACSL proofs
- 100% success rate across all phases

**Status:** Entirely custom NERV work, keep as-is

### 4. Headless/Embedded Optimizations
**Location:** Throughout emu/
**Description:**
- Reduced memory footprint (15-30 MB)
- Fast startup (2 seconds)
- Console-only operation
- No X11 dependency

**Documentation:** docs/HEADLESS-STATUS.md, docs/PERFORMANCE-SPECS.md

### 5. NERV-Specific Applications
**Location:** appl/nerv/
**Files:**
- agent.b - NERV agent framework
- registry.b - Service registry
- spawn.b - Process spawning utilities

**Status:** Entirely custom, keep as-is

### 6. Xenith Text Editor (Acme Fork)
**Location:** appl/xenith/ (on feature/sdl3-gui branch)
**Description:** Complete fork of Acme with custom enhancements
- Streaming PNG/PPM image loading with subsampling
- Adam7 interlaced PNG support for large images
- Auto-display images when opening image files
- AI agent desktop environment ideas
- Extensive modifications and improvements

**Files:** Complete Limbo application (~50+ source files)
**Status:** Entirely custom NERV work, must preserve
**Note:** Currently on feature/sdl3-gui branch, will need to be merged to master/main branch after migration

**Commits:** 20+ commits from pdfinn on Xenith development

### 7. Build System Improvements
**Location:** build-*.sh scripts, various mkfiles
**Description:** Simplified build process for modern systems

### 8. Documentation
**Location:** docs/, *.md files
**Description:** Extensive documentation of 64-bit porting, JIT work, formal verification

**Status:** All custom, keep all

---

## Migration Strategy

### Phase 1: Setup and Preparation

#### 1.1 Add inferno-os as upstream remote
```bash
cd /Users/pdfinn/github.com/NERVsystems/infernode
git remote add inferno-upstream https://github.com/inferno-os/inferno-os.git
git fetch inferno-upstream
```

#### 1.2 Create migration branch
```bash
# Start from current branch (feature/jit-64bit or master)
git checkout -b migration/mit-license
```

**Note about Xenith:** Xenith currently exists on `feature/sdl3-gui` branch.
Options:
1. Perform migration on current branch first, then merge Xenith later
2. Merge feature/sdl3-gui into migration branch first, then do migration
3. Perform migration separately on both branches

**Recommended:** Option 1 - Migrate current branch first (simpler), then merge Xenith and update its license separately.

#### 1.3 Document current state
```bash
# Create snapshot of current working state
git tag snapshot-before-migration
```

#### 1.4 Verify MIT license in upstream
- Download and verify inferno-os NOTICE file
- Confirm MIT licensing is in effect
- Document copyright holders for attribution

### Phase 2: Replace GPL/LGPL Components

#### 2.1 Replace Applications Directory (GPL)
**Strategy:** Replace entire appl/ directory except appl/nerv/ and appl/xenith/

```bash
# Backup NERV applications and Xenith
mkdir /tmp/infernode-custom-backup
cp -r appl/nerv /tmp/infernode-custom-backup/

# If on feature/sdl3-gui branch or after merging it:
# cp -r appl/xenith /tmp/infernode-custom-backup/

# Replace appl/ from upstream
git checkout inferno-upstream/master -- appl/

# Restore NERV applications
cp -r /tmp/infernode-custom-backup/nerv appl/

# Restore Xenith (if backed up)
# cp -r /tmp/infernode-custom-backup/xenith appl/

# Stage changes
git add appl/
```

**IMPORTANT:** If Xenith exists on current branch, must preserve it!

**Verification:**
- Ensure appl/nerv/ still exists
- Ensure appl/xenith/ still exists (if it was on current branch)
- Check that acme, wm, cmd, lib are now MIT-licensed
- Verify NOTICE files show MIT license

#### 2.2 Replace libinterp (LGPL)
**Strategy:** Replace with MIT version, then reapply 64-bit changes

```bash
# Save 64-bit module headers
mkdir /tmp/infernode-64bit-headers
cp libinterp/*mod.h /tmp/infernode-64bit-headers/

# Replace libinterp from upstream
git checkout inferno-upstream/master -- libinterp/

# Restore 64-bit headers (will need regeneration)
# DO NOT copy old headers - they need to be regenerated
```

**CRITICAL:** After replacement, must regenerate module headers with 64-bit limbo:
1. Build 64-bit limbo first
2. Regenerate all module headers
3. Rebuild libinterp

#### 2.3 Replace module/ directory (LGPL)
**Strategy:** Replace with MIT version

```bash
git checkout inferno-upstream/master -- module/
```

**Verification:**
- Ensure NOTICE file shows MIT license
- Verify module interfaces are compatible

#### 2.4 Replace limbo/ compiler
**Strategy:** Replace with MIT version, preserve 64-bit support

```bash
# Replace limbo from upstream
git checkout inferno-upstream/master -- limbo/
```

**CRITICAL:** After replacement, must rebuild limbo with 64-bit settings:
- Ensure mkfile has WORD=intptr
- Rebuild limbo compiler
- Use new limbo to regenerate all module headers

### Phase 3: Apply 64-Bit Changes to New MIT Code

#### 3.1 Identify 64-bit changes
```bash
# Compare current (64-bit) vs upstream (32-bit) for key files
git diff HEAD inferno-upstream/master -- libinterp/
git diff HEAD inferno-upstream/master -- limbo/
```

#### 3.2 Reapply 64-bit patches
For each critical file:
1. Identify WORD/IBY2WD changes
2. Identify pointer size changes
3. Reapply to new MIT version
4. Test compilation

**Key files requiring 64-bit patches:**
- libinterp/dat.h - WORD definition
- libinterp/*.c - Pointer arithmetic
- limbo/stubs.c - Module header generation
- emu/*/dat.h - Platform-specific WORD definitions

#### 3.3 Regenerate 64-bit module headers
```bash
cd libinterp
mk clean
mk sysmod.h loadermod.h drawmod.h mathmod.h keyring.h ipintsmod.h cryptmod.h
mk install
```

Verify headers have 64-bit sizes (not 32-bit).

### Phase 4: Preserve JIT and Emulator Changes

#### 4.1 Audit JIT changes
```bash
# Review JIT-related commits
git log --grep="JIT" --grep="arm64" --grep="AXIMM" --oneline
```

#### 4.2 Merge JIT improvements
If emu/ was not replaced (MIT already), keep as-is.
If emu/ was replaced, cherry-pick JIT commits:
```bash
git cherry-pick <jit-commit-range>
```

### Phase 5: Update License Files

#### 5.1 Replace root LICENCE file
```bash
# Download MIT NOTICE from inferno-os
curl -o NOTICE https://raw.githubusercontent.com/inferno-os/inferno-os/master/NOTICE
curl -o LICENCE https://raw.githubusercontent.com/inferno-os/inferno-os/master/LICENCE 2>/dev/null || true
```

#### 5.2 Update all NOTICE files
Replace GPL/LGPL NOTICE files with MIT versions:
```bash
# For each directory with GPL NOTICE:
for dir in appl libinterp module; do
  git checkout inferno-upstream/master -- $dir/NOTICE
done
```

#### 5.3 Add infernode copyright notice
Create COPYRIGHT file documenting:
- Original Inferno copyrights (Lucent, Vita Nuova, Plan 9 Foundation)
- NERV Systems contributions (64-bit, JIT, formal verification)
- MIT license terms

### Phase 6: Verification and Testing

#### 6.1 Build verification
```bash
# Clean build
mk clean
mk install

# Verify builds without errors
./build-linux-arm64.sh
./build-linux-amd64.sh
```

#### 6.2 Functional testing
```bash
# Test basic functionality
./emu/Linux/o.emu -r.
# ; ls /dis
# ; limbo --version
# ; sh -c 'echo hello'
# ; acme &
```

#### 6.3 64-bit verification
```bash
# Verify 64-bit module headers
grep "size" libinterp/sysmod.h | head -5
# Should show 64-bit sizes (e.g., 144 not 72)
```

#### 6.4 License verification
```bash
# Verify no GPL NOTICE files remain
find . -name NOTICE -exec grep -l "GNU General Public License" {} \;
# Should return empty or only lib/legal/NOTICE.gpl (reference)

# Verify MIT license present
find . -name NOTICE -exec grep -l "MIT" {} \; | head -5
```

### Phase 7: Handle Xenith (feature/sdl3-gui branch)

#### 7.1 Merge feature/sdl3-gui into migration branch
```bash
# After completing migration on main branch
git checkout migration/mit-license
git merge feature/sdl3-gui
```

#### 7.2 Verify Xenith is preserved
```bash
# Check that Xenith still exists
ls appl/xenith/
git log --oneline -- appl/xenith/ | head -5
```

#### 7.3 Update Xenith license status
Since Xenith was originally forked from GPL'd Acme but has been extensively modified:
- Document that Xenith is now based on MIT-licensed Acme from inferno-os
- Update any NOTICE files in appl/xenith/ to reflect MIT license
- Add copyright notice for NERV modifications

**Note:** Xenith is derivative of Acme, so original Acme copyrights apply, but now under MIT.

### Phase 8: Documentation Updates

#### 8.1 Update README.md
- Add MIT license badge
- Update copyright notices
- Add attribution to inferno-os
- Mention Xenith as custom Acme fork

#### 8.2 Create MIGRATION-COMPLETE.md
Document:
- What was replaced
- What was preserved (including Xenith)
- License change justification
- Copyright attributions

#### 8.3 Update DIFFERENCES-FROM-STANDARD-INFERNO.md
Note that infernode is now based on MIT-licensed inferno-os, not acme-sac.
Document that Xenith is a custom fork maintained separately.

---

## Verification Checklist

### License Verification
- [ ] All GPL NOTICE files replaced with MIT versions
- [ ] All LGPL NOTICE files replaced with MIT versions
- [ ] Root LICENCE/NOTICE files show MIT license
- [ ] lib/legal/ contains reference copies of all licenses
- [ ] COPYRIGHT file documents all contributors

### Functional Verification
- [ ] Limbo compiler builds and runs
- [ ] Emulator builds (Linux ARM64, AMD64, macOS ARM64)
- [ ] Basic shell works (sh, ls, pwd, date)
- [ ] Acme editor launches and works
- [ ] JIT compiler works (if enabled)
- [ ] Module loading works
- [ ] 9P filesystem works

### 64-Bit Verification
- [ ] Module headers have 64-bit sizes
- [ ] sizeof(WORD) == 8
- [ ] sizeof(void*) == 8
- [ ] Pointer arithmetic correct
- [ ] GC pointer maps correct
- [ ] No "bad magic" pool errors

### Custom Feature Verification
- [ ] formal-verification/ directory intact
- [ ] appl/nerv/ applications present
- [ ] appl/xenith/ present (after merging feature/sdl3-gui)
- [ ] Xenith builds and runs
- [ ] docs/ documentation intact
- [ ] Build scripts work
- [ ] All 178+ pdfinn commits preserved

### Git History Verification
- [ ] Migration branch clean
- [ ] All custom commits preserved
- [ ] History shows clear migration point
- [ ] Tags mark before/after migration

---

## Rollback Plan

If migration fails:

```bash
# Return to pre-migration state
git checkout master
git branch -D migration/mit-license

# Or revert to snapshot
git reset --hard snapshot-before-migration
```

---

## Timeline Estimates

- **Phase 1 (Setup):** 30 minutes
- **Phase 2 (Replace):** 2-3 hours
- **Phase 3 (64-bit reapply):** 4-6 hours
- **Phase 4 (JIT preserve):** 2-3 hours
- **Phase 5 (License update):** 1 hour
- **Phase 6 (Testing):** 4-8 hours
- **Phase 7 (Xenith merge):** 1-2 hours
- **Phase 8 (Documentation):** 2 hours

**Total:** 16-25 hours of focused work

---

## Risk Assessment

### High Risk
- **64-bit module header regeneration** - If done incorrectly, causes pool corruption
  - Mitigation: Extensive testing, compare old vs new headers
- **JIT functionality** - Complex ARM64 code might not merge cleanly
  - Mitigation: Keep detailed commit history, test thoroughly

### Medium Risk
- **Build system compatibility** - Upstream mkfiles might differ
  - Mitigation: Careful comparison, incremental testing
- **API compatibility** - Module interfaces might have changed
  - Mitigation: Incremental replacement, test each component

### Low Risk
- **Documentation** - Can always be fixed later
- **License files** - Straightforward replacement

---

## Success Criteria

Migration is complete when:
1. ✅ All GPL/LGPL code replaced with MIT versions
2. ✅ All 64-bit functionality preserved
3. ✅ All JIT improvements preserved
4. ✅ All custom NERV features intact (nerv/, formal-verification/)
5. ✅ Xenith editor preserved and functional
6. ✅ All tests pass
7. ✅ License audit shows 100% MIT (except lib/legal references)
8. ✅ Build system works on all platforms
9. ✅ Documentation updated

---

## Post-Migration

### Update README.md License Badge
```markdown
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
```

### Create GitHub Issue
Document migration for future reference.

### Update inferno-os Attribution
Consider contributing 64-bit and JIT improvements back to inferno-os upstream.

---

## Contact

For questions about this migration:
- Review git history of 64-bit changes
- Check docs/PORTING-ARM64.md
- Check ARM64-JIT-BREAKTHROUGH-SESSION.md
- Check formal-verification/README.md

---

**Next Steps:**
1. Review this plan
2. Execute Phase 1 (Setup)
3. Begin Phase 2 (Replacement) with careful testing at each step

---

*This migration removes all GPL contamination from Richard Stallman's licenses, as per project requirements.*
