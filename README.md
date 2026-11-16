# VEFt — Android Video Editor Project

- **Repository / Gradle root:** `VEFt`
- **Android app label:** `EVeditor`
- **Application ID / namespace:** `com.evc.app` (preserved to retain the existing installed-app identity)
- **Version:** `0.2.183` (`versionCode 383`)
- **Minimum Android:** API 24
- **Target / Compile SDK:** 35
- **Target ABI:** `armeabi-v7a` (32-bit ARM)

## GitHub Actions and MGit

The workflow is `.github/workflows/android.yml`.

- Push trigger watches **all branches** using `branches: ["**"]`.
- Pull requests and manual runs are enabled (`workflow_dispatch`).
- Uses JDK 17, Android SDK 35 / Build Tools 35.0.0, and Gradle 8.9.
- Builds the debug APK and uploads `VEFt-0.2.183-ARM32-Dynamic-Storyboard-debug-apk`.

The workflow's all-branches trigger is intentionally retained to avoid the earlier issue where a Commit/Push on a branch other than `main` or `master` did not start a build.

## Fresh repository setup

This package contains no `.git` directory and no configured Git remote. Extract the ZIP and open the **VEFt** folder as the local project/repository in MGit. Initialize a new local Git repository, stage all files including the hidden `.github` directory, and create the first Commit.

Create a new **empty** GitHub repository named exactly `VEFt`, then add its HTTPS address as the remote in MGit and Push the branch. Do not put the project inside an extra nested folder.

## Preserved Android identity

The Android `applicationId`, namespace, source package, and app label are intentionally unchanged. This avoids turning a project/repository rename into an unintended Android app identity change.

## Verification status

- ZIP integrity and project file structure were checked during packaging.
- XML layout/manifest files were parsed.
- Workflow trigger and project/artifact naming were checked for consistency.
- A full Android Gradle build and on-device test have **not** been run here; the first GitHub Actions run must confirm compilation and APK generation.
