@echo off
chcp 65001 >nul
REM 在仓库根目录下双击本文件，或在该目录执行：tools\build_exe.bat
REM 产物：dist\rsa_solver_v4.2.exe（单文件，免装 Python）
cd /d "%~dp0.."

echo [1/2] 检查 / 安装 PyInstaller
python -m pip install --upgrade pyinstaller >nul || goto :fail

echo [2/2] 打包
python -m PyInstaller --onefile --noconfirm --clean --name rsa_solver_v4.2 win_entry.py || goto :fail

echo.
echo 完成：dist\rsa_solver_v4.2.exe
dir /b dist\rsa_solver_v4.2.exe
pause
exit /b 0

:fail
echo.
echo 打包失败，看上面的报错。常见原因：没装 Python，或 python 不在 PATH 里。
pause
exit /b 1
