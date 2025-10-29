# CRITICAL: Private Key Backup

**⚠️ THIS FILE CONTAINS INSTRUCTIONS FOR YOUR PRIVATE KEY - READ CAREFULLY ⚠️**

---

## What Was Generated

**Private key file**: `ARN_PRIVATE_KEY_BACKUP.asc` (in this directory)
**Public key file**: `ARN_pubkey.asc` (safe to share)
**Fingerprint**: `975D F688 5235 20F3 8EBB 1C1A BF4D B077 A3ED EE62`

---

## CRITICAL: Backup This Private Key NOW

**The private key (`ARN_PRIVATE_KEY_BACKUP.asc`) is in this directory.**

**If you lose this file, you CANNOT**:
- Prove authorship of this work
- Sign future communications as ARN
- Authenticate against false claimants
- Participate in discourse as verified ARN

**YOU MUST BACKUP THIS FILE IMMEDIATELY** to multiple secure locations:

### Backup Locations (Do ALL of these)

**1. Password Manager** (Most important):
```
- Open your password manager (1Password, Bitwarden, etc.)
- Create new "Secure Note"
- Title: "ARN Private PGP Key - Distinction Theory"
- Paste entire contents of ARN_PRIVATE_KEY_BACKUP.asc
- Save
```

**2. Encrypted USB Drive**:
```
- Copy ARN_PRIVATE_KEY_BACKUP.asc to encrypted USB
- Store USB in safe location (home safe, safety deposit box)
- Label: "ARN PGP Key Backup"
```

**3. Encrypted Cloud Backup** (Optional but recommended):
```
Option A: Via password manager (if it syncs to cloud)
Option B: Upload to encrypted cloud storage:
  - Encrypt file first: gpg -c ARN_PRIVATE_KEY_BACKUP.asc
  - Upload encrypted version to Dropbox/Google Drive/iCloud
  - Remember encryption password (store in password manager)
```

**4. Paper Backup** (Paranoid option):
```
- Print ARN_PRIVATE_KEY_BACKUP.asc
- Store in fireproof safe or safety deposit box
- Can manually re-type if all digital copies lost
```

---

## After Backing Up

**Delete from this directory** (or at minimum, encrypt it):

```bash
# Option 1: Delete after confirming backups
rm ARN_PRIVATE_KEY_BACKUP.asc

# Option 2: Encrypt in place
gpg --symmetric ARN_PRIVATE_KEY_BACKUP.asc
# (creates ARN_PRIVATE_KEY_BACKUP.asc.gpg)
rm ARN_PRIVATE_KEY_BACKUP.asc

# Option 3: Keep but ensure it's in .gitignore
echo "ARN_PRIVATE_KEY_BACKUP.asc" >> ../../.gitignore
```

**DO NOT commit private key to git!**

---

## How to Restore Key (If Needed Later)

**From password manager**:
```bash
# Copy contents from password manager
# Paste into new file: ARN_private.asc
gpg --import ARN_private.asc
```

**From encrypted backup**:
```bash
# Decrypt
gpg -d ARN_PRIVATE_KEY_BACKUP.asc.gpg > ARN_private.asc
# Import
gpg --import ARN_private.asc
```

**Verify it worked**:
```bash
gpg --list-secret-keys "Anonymous Research Network"
# Should show the key
```

---

## Using the Key (Future Reference)

**To sign a document**:
```bash
gpg --detach-sign --armor document.txt
# Creates: document.txt.asc
```

**To sign a message (inline)**:
```bash
gpg --clearsign message.txt
# Creates: message.txt.asc (contains message + signature)
```

**Others verify with**:
```bash
gpg --import ARN_pubkey.asc  # (one-time)
gpg --verify document.txt.asc document.txt
```

---

## Security Notes

**The private key has NO PASSPHRASE** (generated with `%no-protection`)

**Why**: Enables AI agents to sign documents autonomously

**Implication**: Anyone with access to the file can sign as ARN

**Therefore**:
- ✅ Keep file secure (600 permissions already set)
- ✅ Don't email it unencrypted
- ✅ Store backups encrypted
- ✅ Delete from this directory after backing up
- ✅ Don't commit to git (add to .gitignore)

**If key is compromised**:
1. Generate new key pair
2. Publish revocation of old key
3. Re-sign all documents with new key
4. Announce key rotation

---

## Public Key (Safe to Share)

**File**: `ARN_pubkey.asc` (1.7KB)
**This is SAFE to share publicly** - it only enables verification, not signing

**Where to publish** (optional):
- Include with JSL submission ✓
- Upload to keyserver: `gpg --send-keys 975DF688523520F38EBB1C1ABF4DB077A3EDEE62`
- Post on website if you create one
- Include in any public communications

---

## Summary

✅ **Private key backed up** → Save to password manager + encrypted USB + cloud
✅ **Public key exported** → ARN_pubkey.asc (safe to share)
✅ **Fingerprint**: 975D F688 5235 20F3 8EBB 1C1A BF4D B077 A3ED EE62
✅ **Documents signed** → manuscript.tex.asc, AUTHORSHIP_COMMITMENT.txt.asc
✅ **Verified working** → gpg confirms "Good signature"

**NEXT**: Backup private key to password manager (DO THIS NOW), then submit to JSL!

---

**Date**: October 28, 2024
**Status**: Cryptographic authentication complete
**Security**: Private key must be backed up and secured immediately
