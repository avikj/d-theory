# PGP Key Setup Instructions

## Why We're Doing This

**Problem**: You want to remain somewhat anonymous but need to:
- Prevent false claimants (the "Satoshi problem")
- Authenticate communications if work gets attention
- Participate in scientific discourse without full doxxing

**Solution**: Cryptographic commitment using PGP signatures

---

## Step-by-Step Setup (30 minutes)

### Step 1: Install GPG

**macOS**:
```bash
brew install gnupg
```

**Linux**:
```bash
sudo apt-get install gnupg
```

**Windows**:
Download GPG4Win: https://gpg4win.org/

### Step 2: Create Anonymous Email (Optional but Recommended)

1. Go to protonmail.com
2. Create account: `anon-research-distinction@protonmail.com` (or similar)
3. ProtonMail has built-in PGP support
4. Save credentials securely

**Alternative**: Use your real email if you're using "Coordinated by Avik Jain" framing

### Step 3: Generate PGP Key Pair

```bash
gpg --full-generate-key
```

**When prompted, enter**:
```
Please select what kind of key you want:
   (1) RSA and RSA (default)

   → Press 1 [ENTER]

What keysize do you want? (3072)
   → Type: 4096 [ENTER]
   (Stronger encryption)

Please specify how long the key should be valid.
   → Type: 0 [ENTER]
   (Key does not expire - important for long-term verification)

Key is valid for? (0)
   → Confirm: y [ENTER]

Real name:
   → Type: Anonymous Research Network [ENTER]

Email address:
   → Type: anon-research-distinction@protonmail.com [ENTER]
   (Or your real email if using "Coordinated by Avik Jain")

Comment:
   → Type: Distinction Theory Research [ENTER]
   (Optional descriptor)

Change (N)ame, (C)omment, (E)mail or (O)kay/(Q)uit?
   → Type: O [ENTER]

Enter passphrase:
   → Type a STRONG passphrase [ENTER]
   → Confirm passphrase [ENTER]

   IMPORTANT: Save this passphrase in password manager!
   You'll need it to sign documents.
```

**GPG will generate keys** (takes 1-2 minutes - move mouse/type to create entropy)

### Step 4: Get Your Key Fingerprint

```bash
gpg --list-keys --fingerprint "Anonymous Research Network"
```

**Output will look like**:
```
pub   rsa4096 2024-10-28 [SC]
      ABCD 1234 EFGH 5678 IJKL 9012 MNOP 3456 QRST 7890
uid           [ultimate] Anonymous Research Network <anon-research@protonmail.com>
sub   rsa4096 2024-10-28 [E]
```

**Copy the fingerprint** (the long hex string: ABCD 1234 EFGH... etc.)

### Step 5: Export Public Key

```bash
# Export public key (shareable)
gpg --armor --export anon-research-distinction@protonmail.com > ARN_pubkey.asc

# This creates a file: ARN_pubkey.asc
# This is SAFE to share publicly
```

**Check it was created**:
```bash
cat ARN_pubkey.asc
```

Should see:
```
-----BEGIN PGP PUBLIC KEY BLOCK-----
[long string of characters]
-----END PGP PUBLIC KEY BLOCK-----
```

### Step 6: Backup Your Private Key (CRITICAL)

```bash
# Export private key (KEEP SECRET)
gpg --armor --export-secret-keys anon-research-distinction@protonmail.com > ARN_private_key.asc

# IMMEDIATELY secure this file:
chmod 600 ARN_private_key.asc

# Store in multiple secure locations:
# 1. Password manager (1Password, Bitwarden, etc.)
# 2. Encrypted USB drive
# 3. Secure cloud backup (encrypted)
```

**⚠️ WARNING**: If you lose this private key, you CANNOT prove authorship later!

### Step 7: Update Commitment Document

```bash
cd submissions/godel_incompleteness_jsl/

# Edit AUTHORSHIP_COMMITMENT.txt
# Replace "[TO BE GENERATED]" with your actual fingerprint
```

Use your text editor to replace:
```
PGP Public Key Fingerprint: [TO BE GENERATED]
```

With:
```
PGP Public Key Fingerprint: ABCD 1234 EFGH 5678 IJKL 9012 MNOP 3456 QRST 7890
```

### Step 8: Sign the Commitment Document

```bash
gpg --clearsign AUTHORSHIP_COMMITMENT.txt
```

This creates: `AUTHORSHIP_COMMITMENT.txt.asc` (signed version)

**Or** detached signature (keeps original file separate):
```bash
gpg --detach-sign --armor AUTHORSHIP_COMMITMENT.txt
```

Creates: `AUTHORSHIP_COMMITMENT.txt.asc` (signature file)

### Step 9: Sign the Manuscript

```bash
gpg --detach-sign --armor manuscript.tex
```

Creates: `manuscript.tex.asc`

### Step 10: Verify Everything Works

```bash
# Test verification
gpg --verify AUTHORSHIP_COMMITMENT.txt.asc AUTHORSHIP_COMMITMENT.txt

# Should output:
# gpg: Signature made [date]
# gpg:                using RSA key [fingerprint]
# gpg: Good signature from "Anonymous Research Network <...>"
```

If you see "Good signature", SUCCESS! ✅

---

## What to Include in JSL Submission

**Upload these files**:
1. ✅ `manuscript.tex` (the paper)
2. ✅ `manuscript.tex.asc` (cryptographic signature)
3. ✅ `AUTHORSHIP_COMMITMENT.txt` (commitment document)
4. ✅ `AUTHORSHIP_COMMITMENT.txt.asc` (signature of commitment)
5. ✅ `ARN_pubkey.asc` (public key for verification)
6. ✅ `SUBMISSION_COVER_LETTER.txt` (existing cover letter)
7. ✅ `SUBMISSION_ABSTRACT_EXTENDED.txt` (existing abstract)

**Note in cover letter**: Add paragraph:
```
AUTHORSHIP AUTHENTICATION: To enable future verification while
preserving anonymity, we provide cryptographic signatures using PGP.
The commitment document (AUTHORSHIP_COMMITMENT.txt) explains the
authentication mechanism and discloses AI collaboration. All files
can be verified using the provided public key.
```

---

## How to Use This Later (If Work Gets Attention)

### Scenario: Someone Asks a Technical Question

**1. Write your response** (plain text file):
```
response.txt contains:
---
Regarding the question about Theorem 2.1:

The witness extraction algorithm works as follows...
[your detailed response]

Signed by Anonymous Research Network
October 30, 2024
---
```

**2. Sign it**:
```bash
gpg --clearsign response.txt
```

**3. Send**: `response.txt.asc` (contains message + signature)

**4. Recipient verifies**:
```bash
gpg --import ARN_pubkey.asc  # (one-time, if they haven't already)
gpg --verify response.txt.asc

# Output: "Good signature from Anonymous Research Network"
```

**Result**: They know it's authentically from you, but you stay anonymous.

### Scenario: False Claimant Emerges

**Someone claims**: "I wrote that paper!"

**You respond** (post publicly):
```
AUTHENTICATION CHALLENGE
========================

A false claim to authorship has been made.

I challenge the claimant to sign the following statement with
the private key committed at submission (October 2024, fingerprint:
ABCD 1234 EFGH...):

"I am the author of 'Gödel's Incompleteness Theorems from
Information-Theoretic Bounds' submitted to JSL in October 2024."

[Signed with ARN private key - signature file attached]
---

The claimant cannot produce this signature. I can and have.
```

**End of discussion.** Cryptographic proof is irrefutable.

---

## Security Best Practices

### DO:
- ✅ Use strong passphrase (20+ characters, random)
- ✅ Store private key in multiple secure locations
- ✅ Test verification before submitting
- ✅ Keep private key truly private (never email/share)
- ✅ Use the key consistently for all ARN communications

### DON'T:
- ❌ Share private key with anyone
- ❌ Store private key unencrypted in cloud
- ❌ Use weak passphrase
- ❌ Forget your passphrase (store in password manager!)
- ❌ Sign documents you didn't write

---

## Troubleshooting

**Problem**: "gpg: command not found"
→ Install GPG (see Step 1)

**Problem**: "No secret key"
→ You need to generate key first (Step 3)

**Problem**: "Bad signature"
→ File was modified after signing, or wrong key used

**Problem**: "Can't create signature"
→ Check you entered passphrase correctly

**Problem**: "Key expired"
→ Make sure you selected "0" (no expiration) during generation

---

## Quick Reference Commands

```bash
# List your keys
gpg --list-keys

# Sign a file (detached signature)
gpg --detach-sign --armor filename.txt

# Verify a signature
gpg --verify filename.txt.asc filename.txt

# Export public key
gpg --armor --export email@example.com > pubkey.asc

# Import someone's public key
gpg --import their_pubkey.asc
```

---

## Timeline

**Today**:
- [ ] Install GPG
- [ ] Generate key pair
- [ ] Export/backup keys

**Tomorrow**:
- [ ] Update AUTHORSHIP_COMMITMENT.txt with fingerprint
- [ ] Sign commitment document
- [ ] Sign manuscript
- [ ] Verify all signatures work

**Before submission**:
- [ ] Include all signed files in JSL upload
- [ ] Add note about authentication to cover letter
- [ ] Test that verification works

**Total time**: ~1 hour including setup, testing, documentation

---

## Why This Solves Your Problem

**Before PGP**:
- Anonymous → can't authenticate later
- No way to prove "I'm the real author"
- False claimants can emerge
- Can't participate in discourse

**After PGP**:
- ✅ Anonymous now, authenticated if needed later
- ✅ Cryptographic proof of authorship (unforgeable)
- ✅ False claimants instantly disproven
- ✅ Can participate in discourse with verified identity
- ✅ Option to reveal identity later (but not required)

**You've solved the Satoshi problem.** Congratulations, this is sophisticated operational security.

---

## Need Help?

If you get stuck:
1. Check GPG documentation: https://gnupg.org/documentation/
2. PGP tutorial: https://www.gnupg.org/gph/en/manual.html
3. Ask me (Claude) - I can help debug specific errors

---

**Bottom line**: 1 hour of setup gives you permanent authentication capability while preserving anonymity. This is the right solution for your goals.
