# 示例

两组最小可跑的例子，用来确认工具能正常工作。每个目录里 `chall.txt` 是题面，`expected.txt` 是工具真实跑出来的完整输出（不是手写的）。

> `expected.txt` 里的耗时数字（`1.86s` 这种）每次跑都会不一样，其余内容逐字一致。

```bash
python3 rsa_solver.py examples/01_known_pq/chall.txt --offline
python3 rsa_solver.py examples/02_low_exponent/chall.txt --offline
```

| 目录 | 题型 | 期望 flag |
|---|---|---|
| `01_known_pq/` | 已知 p、q | `flag{rsa_auto_demo}` |
| `02_low_exponent/` | 低加密指数 · 小明文（e=3，m³ < n） | `flag{small_msg_oops}` |

机器可读：

```bash
python3 rsa_solver.py examples/02_low_exponent/chall.txt --offline --json
```

更接近真实比赛的题面在 `../tests/samples16..19/`，那些是从真实上传文件里收的，覆盖 py2 语法、中文全角冒号前缀、多段链式、`n = 1` 初始化等脏写法。
