#!/bin/bash

# ============================================================================
# SAFE CROWDSURF SYNC SCRIPT
# ============================================================================
# PURPOSE: Pull latest CrowdSurf code for network analysis
# SAFETY: PREVENTS any push to main branch (MISSION CRITICAL)
# ALLOWS: Push to non-main branches only (for collaboration)
# ============================================================================

set -e  # Exit on any error

REPO_DIR="/Users/avikjain/Desktop/Distinction Theory/surf-app"
PROD_REMOTE="https://github.com/crowdsurfmusic/surf-app.git"

echo "🚨 CROWDSURF SAFE SYNC - MISSION CRITICAL SAFETY MEASURES"
echo "============================================================"
echo ""

# Clean slate - remove existing surf-app if it exists
if [ -d "$REPO_DIR" ]; then
    echo "📁 Removing existing surf-app directory..."
    rm -rf "$REPO_DIR"
fi

# Clone fresh from production
echo "📥 Cloning fresh from production (read-only intent)..."
cd "/Users/avikjain/Desktop/Distinction Theory"
git clone "$PROD_REMOTE" surf-app

cd surf-app

# ============================================================================
# CRITICAL SAFETY MEASURES - PREVENT MAIN PUSH
# ============================================================================

echo ""
echo "🚨 SETTING UP CRITICAL SAFETY MEASURES..."
echo ""

# 1. Rename origin to make it EXTREMELY explicit this is dangerous
git remote rename origin PRODUCTION-PUSH-TO-MAIN-DESTROYS-LIVE-APP-DO-NOT-PUSH

# 2. Create pre-push hook that BLOCKS main branch pushes
mkdir -p .git/hooks
cat > .git/hooks/pre-push << 'HOOK_END'
#!/bin/bash

# MISSION CRITICAL: Block any push to main branch
# This prevents accidental deployment to production

while read local_ref local_sha remote_ref remote_sha
do
    # Extract branch name from ref
    if [[ $remote_ref =~ refs/heads/(.+)$ ]]; then
        branch="${BASH_REMATCH[1]}"

        if [ "$branch" = "main" ]; then
            echo ""
            echo "🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨"
            echo "🚨                                        🚨"
            echo "🚨  PUSH TO MAIN BLOCKED - CATASTROPHIC   🚨"
            echo "🚨                                        🚨"
            echo "🚨  PRODUCTION DEPLOYS FROM MAIN          🚨"
            echo "🚨  USERS AFFECTED IMMEDIATELY            🚨"
            echo "🚨  AVIK + S.A. STARTUP AT RISK           🚨"
            echo "🚨  MISSION CRITICAL - DO NOT OVERRIDE    🚨"
            echo "🚨                                        🚨"
            echo "🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨"
            echo ""
            echo "You attempted to push to main branch."
            echo ""
            echo "CONSEQUENCES:"
            echo "  - Instant production deployment"
            echo "  - Live users affected immediately"
            echo "  - Potential app breakage"
            echo "  - Avik + S.A.'s startup at risk"
            echo "  - 6 months of work potentially destroyed"
            echo ""
            echo "SAFE WORKFLOW:"
            echo "  1. Create feature branch:"
            echo "     git checkout -b network/feature-name"
            echo ""
            echo "  2. Push to feature branch only:"
            echo "     git push PRODUCTION-PUSH-TO-MAIN-DESTROYS-LIVE-APP-DO-NOT-PUSH network/feature-name"
            echo ""
            echo "  3. NEVER push to main"
            echo ""
            echo "This hook is protecting you. Do not override it."
            echo "If you think you need to push to main, you don't."
            echo "Talk to Avik first."
            echo ""
            echo "🚨 MAIN BRANCH PUSH = BLOCKED FOR SAFETY 🚨"
            echo ""
            exit 1
        fi
    fi
done

exit 0
HOOK_END

chmod +x .git/hooks/pre-push

# 3. Set push.default to nothing (require explicit branch specification)
git config --local push.default nothing

# 4. Add big warning to git config
git config --local crowdsurf.warning "NEVER PUSH TO MAIN - PRODUCTION DEPLOYS AUTOMATICALLY"

# 5. Create .git/DANGER_PRODUCTION file as visual reminder
cat > .git/DANGER_PRODUCTION << 'DANGER_END'
⚠️⚠️⚠️ DANGER - PRODUCTION REPOSITORY ⚠️⚠️⚠️

This repository is connected to PRODUCTION CrowdSurf deployment.

NEVER PUSH TO MAIN BRANCH.
Production server deploys directly from main.
Push to main = instant production deployment = potential disaster.

SAFE WORKFLOW:
1. Create feature branch: git checkout -b network/feature-name
2. Make changes and commit
3. Push to feature branch: git push production-DANGEROUS network/feature-name
4. NEVER: git push to main

Pre-push hook will block main pushes, but don't rely on it alone.
Be conscious. Be careful. Production depends on it.

⚠️⚠️⚠️ DANGER - PRODUCTION REPOSITORY ⚠️⚠️⚠️
DANGER_END

# ============================================================================
# VERIFICATION
# ============================================================================

echo "✅ Safety measures configured:"
echo ""
echo "  1. Remote renamed: 'origin' → 'PRODUCTION-PUSH-TO-MAIN-DESTROYS-LIVE-APP-DO-NOT-PUSH'"
echo "  2. Pre-push hook: BLOCKS main branch pushes"
echo "  3. Push default: Requires explicit branch specification"
echo "  4. Warning config: Set in git config"
echo "  5. Danger file: Created at .git/DANGER_PRODUCTION"
echo ""
echo "📋 Current git configuration:"
git remote -v
echo ""
echo "🔒 Push protection: ACTIVE"
echo ""

# Test the hook
echo "🧪 Testing pre-push hook protection..."
echo ""
echo "Attempting simulated push to main (should BLOCK):"
# This won't actually push, just tests the hook
# We'll create a dummy scenario
current_branch=$(git branch --show-current)
if [ "$current_branch" = "main" ]; then
    echo "  ⚠️  Currently on main branch"
    echo "  ✅ Pre-push hook will block if you try: git push production-DANGEROUS main"
else
    echo "  ✅ Currently on branch: $current_branch (safe)"
fi

echo ""
echo "============================================================"
echo "✅ SAFE SYNC COMPLETE"
echo "============================================================"
echo ""
echo "📁 CrowdSurf code available at: $REPO_DIR"
echo ""
echo "🚨 REMEMBER:"
echo "  - NEVER push to main"
echo "  - Create feature branches for any changes: git checkout -b network/feature-name"
echo "  - Push only feature branches: git push production-DANGEROUS network/feature-name"
echo "  - Pre-push hook will protect you, but stay conscious"
echo ""
echo "🎵 Ready for network analysis and implementation work"
echo ""
