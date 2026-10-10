@echo off
setlocal
set "mec_exit_code=2"
title MEC H offline reproduction
echo Running the existing offline MEC reproduction.
echo Default: 256-bit subgroup, n=16, seed=20261009, b0=7.
echo.

python -c "import sys; sys.exit(0 if sys.version_info >= (3, 9) else 1)" >nul 2>nul
if not errorlevel 1 goto :run_python

py -3 -c "import sys; sys.exit(0 if sys.version_info >= (3, 9) else 1)" >nul 2>nul
if not errorlevel 1 goto :run_py

echo RESULT: NOT RUN
echo Python 3.9 or newer was not found through python or py -3.
echo No dependencies were installed and no system settings were changed.
goto :finished

:run_python
python -B "%~dp0run_local.py" %*
set "mec_exit_code=%errorlevel%"
goto :finished

:run_py
py -3 -B "%~dp0run_local.py" %*
set "mec_exit_code=%errorlevel%"

:finished
echo.
echo See mec\README.md for instructions and boundaries.
pause
exit /b %mec_exit_code%
