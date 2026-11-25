# 发布步骤（README 是给人看的，这份是给伸手就能走完的）

仓库已经是「解压即用」状态，`git init` + 第一次 commit 已经做过。你只需要建远程仓库、推上去、挂 exe。

---

## 一、先改成你自己的提交身份

```bash
git config user.name  "你的名字"
git config user.email "你的邮箱"
git commit --amend --reset-author --no-edit
```

（不改的话提交记录里是默认身份，不影响功能，只是不好看。）

---

## 二、GitHub 建空仓库

1. 打开 https://github.com/new
2. 仓库名 `rsa-auto`（想用别的名字就同步改 README 里的 clone 地址和 CI 徽章路径）
3. **不要勾** Add a README / .gitignore / license —— 仓库里已经有了，勾了会冲突
4. 点 Create repository

---

## 三、推上去

```bash
git remote add origin https://github.com/你的用户名/rsa-auto.git
git push -u origin main
```

### 密码那一步填什么

GitHub 从 2021 年起**不再接受账号密码**做 git 认证，密码框里要填 **Personal Access Token**：

1. https://github.com/settings/tokens → Tokens (classic) → Generate new token (classic)
2. 勾 `repo` 权限（就够）
3. 有效期按自己习惯选，生成后**复制一次**（页面关掉就再也看不到）
4. `git push` 提示 Password 时粘这个 token

不想每次输就用凭证缓存：

```bash
git config --global credential.helper store
```

（会明文存在 `~/.git-credentials`，公共机器别用。）

---

## 四、给仓库补两样东西

**About 栏**（仓库首页右上角齿轮）：
- Description：`33 类 RSA CTF 题型自动判定 + 解密，纯标准库零依赖，不装 gmpy2 不用 Sage`
- Topics：`ctf` `rsa` `cryptography` `ctf-tools` `python` `coppersmith` `boneh-durfee`

**Releases**：见下一节。

---

## 五、发 exe 到 Releases

1. Windows 上双击 `tools/build_exe.bat`（需要装 Python 3.8+），生成 `dist\rsa_solver_v4.2.exe`
2. 仓库右侧 Releases → Draft a new release
3. Tag 填 `v4.2.0`，标题 `v4.2`
4. 把 exe 拖进附件区
5. 说明里写一句：解压即用，可拖拽题目文件，也可直接粘题面；默认纯本地不联网

exe 大约 7.5 MB，`*.exe` 已在 `.gitignore` 里，不会进仓库。

---

## 六、推完之后确认三件事

```bash
git remote -v          # 指向你自己的仓库
git log --oneline      # 有第一次提交
git status             # working tree clean
```

然后打开 GitHub 页面看：
- README 正常渲染，表格没崩
- Actions 里 CI 开始跑（3.8 / 3.11 / 3.13 / Windows 四个 job），全绿后徽章会自动变绿
- 徽章里如果还写着 `<你的用户名>`，用编辑器全局替换成你的用户名再提交一次

---

## 七、后面改代码的流程

```bash
git add -A
git commit -m "fix: 描述改了什么"
git push
```

- **别把整个 `samples/` 目录塞进仓库当题库**——现在这 19 组是真实题面回归用的，加公开题库会让仓库变重、也会有人直接搜答案
- 改 `rsa_solver.py` 之后**先跑 `python3 tests/run_all.py`**，25 项全绿再推，别让 CI 红着进 main
- 版本号在 `rsa_solver.py` 第 20 行 `__version__`，BANNER 自动拼，改一处就够

---

## 常见问题

**push 报 `Support for password authentication was removed`**
→ 用 token，不是密码。见第三节。

**push 报 `failed to push some refs` / `rejected`**
→ 远程仓库建的时候勾了 README，本地和远程各有一个提交。最省事的办法是删掉远程仓库重建（不勾任何文件），或者：
```bash
git pull --rebase origin main
git push -u origin main
```

**CI 里 Windows job 中文乱码 / UnicodeEncodeError**
→ 工作流里已经设了 `PYTHONIOENCODING=utf-8`；本地自己跑测试时也一样：
```powershell
$env:PYTHONIOENCODING="utf-8"; python tests/run_all.py
```
