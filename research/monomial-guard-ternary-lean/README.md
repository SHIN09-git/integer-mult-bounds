# 三元域完整主子式代价界的 Lean 验证

**2026-11-07：验证通过。** 编译、40 条关键声明的公理检查，以及包含全部导入依赖的新环境内核重放均已完成。完整重放耗时约 528 秒。详见 [验证摘要](verification/SUMMARY.json) 和 [原始结果](verification/RESULT.json)。

本项目在上一版 \(h-Z\) 证明的基础上，形式化三元域 \(\mathbb F_3\) 中的结论

\[
\max(S,L)\le C\le 2S+L,
\]

并为每个 \(r,n\in\mathbb N\) 给出 \(S=r,L=n\) 的两组完整仿射族，分别具有精确代价 \(\max(r,n)\) 和 \(2r+n\)。参数没有上限，包含 \(r=0\)、\(n=0\) 及两者同时为零的情形。

原文来自 [PR #6712](https://github.com/CrocSwap/integer-mult-bounds/pull/6712) 的 `GAP.md`，固定在提交 `03caa7f6cb5bd21c834024e9d81f6b43eb325b91`。
原文副本、文件哈希及构造差异见 [来源记录](reference/TERNARY-SOURCE.json)。

## 定理的含义与条件

坐标集 \(I\) 和参数集 \(J\) 均有限。状态为 \(u_i,b_i\in\mathbb F_3\) 及 \(w_i\in\mathbb F_3^J\)，假设

\[
\sum_i u_i b_i=1,\qquad \sum_i u_iw_i=0.
\]

参数行遍历完整仿射族 \(v_i(a)=b_i+\sum_{j\in J}a_jw_i(j)\)，其中 \(a\) 遍历所有 \(\mathbb F_3^J\)。不要求各斜率行线性无关。

- \(h\) 为初始向量值 \(u_iw_i\ne0\) 的坐标数；\(Z\) 为把这些带标识的非零坐标分成非空零和组时，最多能分出的组数。定义 \(S=h-Z\)。
- 将标量 \(u_ib_i\) 按 \(0,1,-1\) 提升到整数，令 \(D=\#\{i:u_ib_i=1\}-\#\{i:u_ib_i=-1\}\)，定义 \(L=\min(|D-1|,|D+2|)/3\)。上述归一化保证 \(D\equiv1\pmod3\)，因此这里的商是整数。
- \(C\) 是使矩阵 \(I-uv(a)\) 对所有参数 \(a\) 的**所有真前缀主子式均非零**所需的最少付费操作数。完整行列式不参与检查。

每次合法行加法 \(R_i\leftarrow R_i+cR_j\) 计一次，要求 \(i\ne j,c\ne0\)，并同时更新对偶行：

\[
u_i\leftarrow u_i+cu_j,\qquad
w_j\leftarrow w_j-cw_i,\qquad
b_j\leftarrow b_j-cb_i.
\]

置换及非零对角缩放免费，可以穿插在任意位置。初始零坐标始终保留，可以被后续操作使用。最小代价的定义只在上述两个归一化条件下解释；Lean 已证明成功序列存在且最小值可达。

`FullGuard` 允许免费选择最终坐标顺序。`fullguard_run_iff` 证明，在 `Fin m` 坐标上，它与原始固定顺序 `HZ.Passes` 有相同的付费可达性。二者使用实际矩阵主子式。

## 已证明的主声明

| 结论 | Lean 声明 |
|---|---|
| 任意合法成功序列至少需要 \(\max(S,L)\) 次 | `Ternary.guard_lower_bound` |
| 存在不超过 \(2S+L\) 次的成功序列 | `Ternary.guard_upper_attained` |
| 最小代价的两侧界 | `Ternary.envelope` |
| 成功恰等于斜率分离且 \(D\in\{1,-2\}\)，允许免费排序 | `Ternary.fullguard_iff` |
| 两种顺序表述的操作代价相同 | `Ternary.fullguard_run_iff` |
| 下端构造的精确最小代价 \(\max(r,n)\) | `Ternary.lower_cost` |
| 上端构造的精确最小代价 \(2r+n\) | `Ternary.upper_cost` |
| 对每个 \(r,n\ge0\)，两端的 \(S,L,C\) 六个等式 | `Ternary.sharp_endpoints` |
| 两端均有相应次数的实际合法操作序列 | `Ternary.lower_attained`、`Ternary.upper_attained` |
| 任意成功方案对上端构造都至少需 \(2r+n\) 次 | `Ternary.upper_word_lower_bound` |
| 包括零参数时，两组构造的斜率行仍非零 | `Ternary.endpoint_nonzero_slopes` |

## 一般界的证明

一次行加法只改变两个标量值，并保持它们在 \(\mathbb F_3\) 中的和。因此整数 \(D\) 的变化绝对值至多为三，\(L\) 每步至多改变一；免费操作保持 \(D,L\)。

对一个完整参数族，如果所有真前缀主子式均非零，上一版证明推出每个 \(u_iw_i=0\)。三元域的排序引理进一步给出整数 \(D=1\) 或 \(D=-2\)。所以任何成功方案既至少需要 \(S\) 次斜率分离，也至少需要 \(L\) 次标量调整，得到下界。

达到上界时，先用 \(S\) 次完成最优斜率分离。新状态的标量代价至多为 \(L+S\)。Lean 随后构造恰好这么多次的标量修复操作，并证明它们保持斜率分离。最后免费排序即可使所有受检主子式通过，总次数至多 \(S+(L+S)\)。

标量修复将两项同号非零标量合并：两项 \(+1\) 变成一项 \(-1\) 和一项零，令 \(D\) 减三；两项 \(-1\) 则令 \(D\) 加三。证明包含每一步系数非零、坐标不同及所需同号坐标存在。

## 两端构造

令 \(a=\min(r,n)\)。每一对斜率坐标初始取 \(u=1\)，斜率分别为 \(+1,-1\)。

| 构造 | \(r\) 对斜率坐标上的标量 | 额外的纯 \(+1\) 标量坐标数 | 精确最小代价 |
|---|---|---:|---:|
| 下端 | \(a\) 对的两项都为 \(+1\)，其余为零 | \(3n+1-2a\) | \(\max(r,n)\) |
| 上端 | 每一对的两项都为 \(-1\) | \(2r+3n+1\) | \(2r+n\) |

两组初始整数差均为 \(D=3n+1\)，因此 \(L=n\)。它们有 \(2r\) 个非零斜率向量值，且可以组成 \(r\) 个相反数对，故 \(S=r\)。

下端先用 \(r\) 次消去斜率对；其中 \(a\) 次同时使 \(D\) 减三。再用 \(n-a\) 次标量修复，总次数 \(r+n-a=\max(r,n)\)，与一般下界相等。

上端先用 \(r\) 次消去斜率对，得到 \(D=3(r+n)+1\)。再用 \(r+n\) 次标量修复，总次数 \(2r+n\)。最优性还需要下面的加强下界。

两组形式化构造都额外保留一个 \(u=0,b=0,w=1\) 的辅助坐标，使 \(r=0\) 时仍然得到非恒定的一参数完整族。原文只在 \(r=0\) 时加入该坐标；这里对所有 \(r\) 统一保留。它可以被任意竞争方案使用，已被下界证明覆盖。因而这仍证明两端可达，但不声称构造维数最小。

## 上端的加强下界

定义标量整数权重
\[
q(0)=0,\quad q(1)=1,\quad q(-1)=2,\qquad W(s)=\sum_iq(u_ib_i).
\]

`Ternary.strong_execution_bound` 证明：若初始状态满足“\(w_i=0\) 的坐标都有 \(u_ib_i=1\)”，则任意使用 \(k\) 次行加法、到达斜率分离状态 \(t\) 的合法序列都满足
\[
W(s)\le3k+D(t).
\]

证明沿操作序列反向合并坐标组。每组记录最终标量的整数提升；模三的标量总和保持不变。若该组初始斜率非零，则其终点必有一个标量零坐标。结合每项提升至少为 \(-1\) 及模三关系，得到每组
\[
W_B\le3(|B|-1)+D_B.
\]
免费置换只搬移组的标签，缩放保持这些条件。合并次数控制组数，将上述式子求和得到整个序列的下界。

成功终点 \(D(t)\in\{1,-2\}\)，所以 \(W(s)\le3k+1\)。上端构造满足前提且 \(W(s)=6r+3n+1\)，从而 \(k\ge2r+n\)。证明覆盖任意操作顺序，也覆盖额外的零标量辅助坐标。

## 文件入口

| 文件 | 内容 |
|---|---|
| [Ternary/Scalar.lean](Ternary/Scalar.lean) | 三元域整数提升、\(S,L,D\) 定义和单步代价变化 |
| [Ternary/Ordering.lean](Ternary/Ordering.lean) | 合法前缀排序的必要性及存在性 |
| [Ternary/Repair.lean](Ternary/Repair.lean) | 保持分离的精确标量修复 |
| [Ternary/Guard.lean](Ternary/Guard.lean) | 实际主子式与分离、排序条件的等价 |
| [Ternary/Envelope.lean](Ternary/Envelope.lean) | 一般界、最小值可达及固定顺序连接 |
| [Ternary/Components.lean](Ternary/Components.lean) | 任意操作序列的反向分组证书 |
| [Ternary/StrongLower.lean](Ternary/StrongLower.lean) | 权重加强下界 |
| [Ternary/PairFamily.lean](Ternary/PairFamily.lean) | 参数化相反斜率对及实际消去序列 |
| [Ternary/Endpoints.lean](Ternary/Endpoints.lean) | 任意 \(r,n\) 的两端构造与精确最小代价 |
| [HZ/](HZ/) | 上一版的六个证明模块，内容保持不变 |
| [Audit.lean](Audit.lean) | 40 条关键声明的传递公理依赖及主声明签名 |
| [verify.ps1](verify.ps1) | 来源检查、编译、公理检查与完整内核重放 |
| [verification/RESULT.json](verification/RESULT.json) | 最终验证状态、工具信息及验证输入哈希 |

## 复现

需要 Lean 4.24.0 与 PowerShell 7。`lean-toolchain` 固定 Lean 版本，`lake-manifest.json` 固定 mathlib 及其间接依赖。可安装 [elan](https://github.com/leanprover/elan) 管理 Lean，首次获取工具及依赖需要联网。

```text
pwsh -NoProfile -File ./prepare.ps1
git clone --branch v4.24.0 https://github.com/leanprover/lean4checker.git .verification-tools/lean4checker
git -C .verification-tools/lean4checker checkout --detach da26eb05e9959402afcb9bd6dfe5dc4f700f70d6
lake -d .verification-tools/lean4checker build lean4checker
pwsh -NoProfile -File ./verify.ps1 -CheckerExe ./.verification-tools/lean4checker/.lake/build/bin/lean4checker
```

Windows 上给最后的检查器路径加 `.exe`。若已有独立 Lean 安装，可给脚本传入 `-LeanBin`。新运行日志写入 `.verification-runs/`，不覆盖随包保存的验证记录。

只编译并查看公理依赖时运行：

```text
lake build
lake env lean -DwarningAsError=true Audit.lean
```

完整检查包括：

1. 检查七个复用的 HZ 源文件与上一版验证收据一致。
2. 编译所有新模块，把警告视为错误。
3. 扫描本项目证明源码，拒绝证明占位符、新增公理、本机决定过程及绕过内核的设置。
4. 对 40 条关键声明检查传递公理依赖，只允许 `propext`、`Classical.choice`、`Quot.sound`。
5. 用官方 `lean4checker --fresh` 在新环境中重放 `TernaryProofCheck` 及全部导入依赖。
6. 核对被验证输入在运行前后没有变化，成功后才输出 PASS 收据。

源码中的普通 `decide` 由 Lean 内核归约；不使用 `native_decide`。官方检查器仍使用 Lean 的同一内核实现，新环境重放不等于由另一种独立内核证明。

## 范围与来源

本次完成三元域一般界及所有非负参数的两端可达性。原项目的有限枚举、最小维数断言、轨道计数、复杂度归约和动态规划不在本次形式化范围内。两端可达表示固定 \(S,L\)、允许维数变化时上下界均能达到，并未证明区间内每个整数都可达到。这些操作次数也不直接改变整数乘法复杂度指数。

`reference/PRICE-ENVELOPE.json` 是原项目的有限证据副本；参数化定理不依赖这个 JSON。`reference/GAP.md` 原样保留，其中“distance to the set 1$”有排版损坏；形式化使用前文明确的目标集合 \(\{1,-2\}\)。`reference/SOURCE.json` 仅记录继承的 \(h-Z\) 来源，新定理来源由 `reference/TERNARY-SOURCE.json` 记录。

形式化由 SHIN09-git 的研究项目使用 OpenAI Codex 完成。原证明、既有分组思想、行操作及行列式恒等式的署名保留在 [reference/NOTICE](reference/NOTICE)。本项目采用 Apache-2.0，Lean、mathlib 和检查器保留各自许可。数学文字与 Lean 模型的对应关系经过本次 AI 辅助核对，未声称已有外部人工审核或上游验收。

归档只包含本项目源码、引用材料及验证记录，不包含工具二进制或依赖编译缓存。

