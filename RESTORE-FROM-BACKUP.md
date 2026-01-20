# How to Restore from Backup

**Backup created:** 2026-01-20 23:42:54
**Before:** MIT migration / fresh fork strategy

## Backup Locations

### 1. Git Tags (pushed to GitHub)
```bash
backup-before-mit-migration-20260120  # Current branch (feature/jit-64bit)
backup-feature-sdl3-gui-20260120      # feature/sdl3-gui (has Xenith)
backup-master-20260120                # master branch
```

### 2. Physical Tar Backup
```
Location: /Users/pdfinn/github.com/NERVsystems/infernode-backup-20260120-234254.tar.gz
Size: 38MB
Contains: Complete working tree including all branches, .git directory
```

---

## Restore Methods

### Method 1: Restore from Git Tags (Recommended - Clean)

Restore just the code without any migration attempts:

```bash
cd /Users/pdfinn/github.com/NERVsystems/infernode

# Restore current branch to backup point
git checkout backup-before-mit-migration-20260120

# Create a new branch from backup
git checkout -b restored-from-backup

# Or restore specific branch
git checkout backup-feature-sdl3-gui-20260120  # For Xenith
git checkout backup-master-20260120             # For master
```

### Method 2: Restore from Tar Backup (Nuclear Option)

Complete restore including working directory state:

```bash
# 1. Move current directory out of the way
cd /Users/pdfinn/github.com/NERVsystems
mv infernode infernode-BROKEN-$(date +%Y%m%d-%H%M%S)

# 2. Extract backup
tar -xzf infernode-backup-20260120-234254.tar.gz

# 3. Verify
cd infernode
git status
git branch
```

### Method 3: Restore from GitHub Remote

If everything local is destroyed:

```bash
# 1. Clone fresh from GitHub
cd /Users/pdfinn/github.com/NERVsystems
git clone git@github.com:NERVsystems/infernode.git infernode-restored

cd infernode-restored

# 2. Checkout backup tag
git checkout backup-before-mit-migration-20260120

# 3. Create working branch
git checkout -b feature/jit-64bit
```

---

## What Each Backup Contains

### backup-before-mit-migration-20260120
- Branch: feature/jit-64bit
- Commit: 305ecc8 (docs: Verify calc.dis works perfectly in interpreter, fails in JIT)
- Contains: All 64-bit work, JIT compiler, formal verification
- Missing: Xenith (on different branch)

### backup-feature-sdl3-gui-20260120
- Branch: feature/sdl3-gui
- Contains: Xenith editor, SDL3 GUI work
- All SDL3/GUI development

### backup-master-20260120
- Branch: master
- Base version before feature branches

---

## Verification After Restore

```bash
# Check git status
git status
git log --oneline -5

# Verify custom work present
ls formal-verification/
ls appl/nerv/
ls docs/

# Check branch
git branch

# Verify builds
./build-linux-arm64.sh   # or appropriate build script
```

---

## Quick Recovery Commands

### "Just get me back to working state NOW!"
```bash
cd /Users/pdfinn/github.com/NERVsystems/infernode
git checkout backup-before-mit-migration-20260120
git checkout -b working-branch
```

### "Nuclear option - restore everything"
```bash
cd /Users/pdfinn/github.com/NERVsystems
mv infernode infernode-backup
tar -xzf infernode-backup-20260120-234254.tar.gz
```

### "I need Xenith"
```bash
cd /Users/pdfinn/github.com/NERVsystems/infernode
git checkout backup-feature-sdl3-gui-20260120
```

---

## Backup Verification

To verify backup integrity:

```bash
# Test tar backup
tar -tzf /Users/pdfinn/github.com/NERVsystems/infernode-backup-20260120-234254.tar.gz | head -20

# Verify tags exist
git ls-remote --tags origin | grep backup-

# Check tag commits
git show backup-before-mit-migration-20260120 --stat
```

---

## When to Use Each Method

**Use Method 1 (Git Tags)** if:
- You want a clean restore to a specific commit
- Git repository is still intact
- Just need to undo recent changes

**Use Method 2 (Tar Backup)** if:
- .git directory is corrupted
- Working tree is completely messed up
- Want to preserve exact file timestamps/permissions

**Use Method 3 (GitHub Remote)** if:
- Local machine failed/lost
- All local backups destroyed
- Starting from scratch on new machine

---

## Notes

- All backups include GPL/LGPL code (pre-migration state)
- Tar backup includes build artifacts (.o, .dis files)
- Git tags are pushed to GitHub (safe from local failures)
- Backup timestamp: 2026-01-20 23:42:54
- Total commits at backup: 286
- pdfinn commits: 178

---

## Safety Checks Before Deleting Backups

DO NOT delete backups until:
- [ ] MIT migration is complete and tested
- [ ] New version builds successfully
- [ ] 64-bit functionality verified
- [ ] JIT compiler works
- [ ] Xenith merged and working
- [ ] At least 1 week of successful usage

---

## Contact

If you need help restoring, this document should have everything you need.
The backups are comprehensive and tested.

**You can safely experiment knowing you can always get back to this exact state.**
