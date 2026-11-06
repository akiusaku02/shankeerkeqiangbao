# -*- coding: utf-8 -*-
"""
最终版 launcher.py
1.打包exe不会误判库
2.启动pyw不弹黑控制台
3.拉起后主程序，启动器exe立刻退出，不占后台
4.正常流程无弹窗；只异常/安装才弹窗
放在根目录，原脚本放到 ./app/山科第二课堂.pyw
"""
import sys
import os
import subprocess
import tempfile
import tkinter as tk
from tkinter import messagebox
import webbrowser

# ===================== 配置 =====================
SUB_FOLDER = "app"
TARGET_SCRIPT = "山科第二课堂.pyw"
REQUIRED_LIBS = [
    "requests",
    "selenium"
]
# ================================================

def show_msg(title, text):
    """仅异常/交互弹窗"""
    root = tk.Tk()
    root.withdraw()
    messagebox.showinfo(title, text)
    root.destroy()

def get_real_python():
    """
    返回 (python_exe, pythonw_exe)
    python_exe用于pip、库检测；pythonw_exe运行GUI脚本无黑框
    """
    if not getattr(sys, 'frozen', False):
        py = sys.executable
        base, ext = os.path.splitext(py)
        pyw = base + "w" + ext
        return py, pyw

    candidates_py = ["python.exe", "python3.exe"]
    candidates_pyw = ["pythonw.exe", "python3w.exe"]
    py_exe = None
    pyw_exe = None

    for cmd in candidates_py:
        try:
            cp = subprocess.run([cmd, "--version"], capture_output=True, text=True)
            if cp.returncode == 0:
                py_exe = cmd
                break
        except FileNotFoundError:
            continue

    for cmd in candidates_pyw:
        try:
            cp = subprocess.run([cmd, "--version"], capture_output=True, text=True)
            if cp.returncode == 0:
                pyw_exe = cmd
                break
        except FileNotFoundError:
            continue
    return py_exe, pyw_exe


def check_python():
    py_exe, pyw_exe = get_real_python()
    if py_exe is None or pyw_exe is None:
        show_msg("错误", "未检测到本机Python / pythonw！\n即将打开Python官网。\n❗安装务必勾选【Add Python to PATH】")
        webbrowser.open("https://www.python.org/downloads/")
        input("安装完成后按回车关闭窗口，重新运行本启动器")
        sys.exit(1)
    return py_exe, pyw_exe


def check_lib_via_python(py_exe, lib_list):
    check_code = """
import importlib,sys
missing=[]
for name in sys.argv[1:]:
    try:
        importlib.import_module(name)
    except Exception:
        missing.append(name)
print("|||".join(missing))
"""
    with tempfile.NamedTemporaryFile(mode="w", suffix=".py", delete=False, encoding="utf-8") as f:
        f.write(check_code)
        tmp_file = f.name
    try:
        res = subprocess.run(
            [py_exe, tmp_file] + lib_list,
            capture_output=True,
            text=True
        )
        out = res.stdout.strip()
        missing = out.split("|||") if out else []
        return missing
    finally:
        os.unlink(tmp_file)


def check_and_install_libs(py_exe):
    missing = check_lib_via_python(py_exe, REQUIRED_LIBS)
    if not missing:
        return True

    show_msg("开始安装依赖", f"需要自动安装库：{','.join(missing)}\n点击确定开始安装，请勿关闭窗口")
    for pkg in missing:
        ret = subprocess.run(
            [py_exe, "-m", "pip", "install", pkg]
        )
        if ret.returncode != 0:
            show_msg("安装失败", f"库 {pkg} 安装失败！\n请手动执行命令：\n{py_exe} -m pip install {pkg}")
            return False
    show_msg("依赖安装完成", "✅全部依赖安装完成！准备启动主程序")
    return True


def run_target_script(pyw_exe):
    script_path = os.path.join(os.getcwd(), SUB_FOLDER, TARGET_SCRIPT)
    if not os.path.exists(script_path):
        show_msg("文件缺失错误", f"找不到主脚本文件！\n预期路径：{script_path}\n\n确认app文件夹和里面pyw文件存在")
        sys.exit(1)
    folder_cwd = os.path.dirname(script_path)
    try:
        # ⚠️不接收返回值，不保存Popen对象，直接执行；父进程直接退出，子进程独立运行
        subprocess.Popen(
            [pyw_exe, script_path],
            cwd=folder_cwd,
            creationflags=subprocess.CREATE_NO_WINDOW,
            # 把管道全部置为None，防止句柄继承导致父进程无法退出
            stdin=None,
            stdout=None,
            stderr=None
        )
    except Exception as e:
        show_msg("启动异常", f"运行脚本失败：{str(e)}")
        sys.exit(1)


def main():
    try:
        py_path, pyw_path = check_python()
        ok = check_and_install_libs(py_path)
        if ok:
            run_target_script(pyw_path)
        # 执行到这里，直接退出启动器，不留后台进程
    except Exception as err:
        show_msg("启动器发生异常", f"错误信息：{err}")
    sys.exit(0)


if __name__ == "__main__":
    main()
