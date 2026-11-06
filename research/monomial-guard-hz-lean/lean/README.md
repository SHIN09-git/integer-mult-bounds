# 整数乘法研究：h − Z 最优行加法次数的 Lean 验证

**2026-11-07：验证通过。** 编译、公理白名单检查和包含全部导入依赖的新环境内核重放均已完成；完整重放耗时约 651 秒。详见 [验证摘要](verification/SUMMARY.json) 和 [原始结果](verification/RESULT.json)。

本项目形式化 [PR #6712](https://github.com/CrocSwap/integer-mult-bounds/pull/6712)
中“斜率分离的最优代价等于 h − Z”的定理，并证明原文锚定情形下的完整主子式结论。
原证明固定在提交 `03caa7f6cb5bd21c834024e9d81f6b43eb325b91`；副本、来源和许可见
[`reference/`](reference/)。这份形式化使用 Lean 4.24.0 和固定提交的 mathlib。

## 验证的数学命题

在固定的有限坐标集 `I` 上，状态包含列向量 `u`、向量值的对偶行 `w`，以及标量行 `b`。
每个坐标的斜率向量值为 `yᵢ = uᵢ • wᵢ`，假设所有 `yᵢ` 的和为零。

- `h` 是初始 `yᵢ ≠ 0` 的坐标数量。
- `Z` 是把这些带有独立标识的非零坐标分成**非空、互不相交、覆盖全部非零坐标的零和组**时，最多能分出的组数。
- 置换和非零对角缩放免费；每次 `Rᵢ ← Rᵢ + a Rⱼ` 计一次，要求 `i ≠ j`、`a ≠ 0`。
- 操作同时按逆作用更新对偶行：`wⱼ ← wⱼ − a • wᵢ`，`bⱼ ← bⱼ − a bᵢ`。

**使每个斜率向量值都变成零所需的最少付费操作次数，恰好等于 `h − Z`。**
初始为零的坐标始终保留在状态中，可以在操作中用作辅助。免费操作允许穿插在任何位置。
相同的向量值不会合并坐标标识。空的非零坐标集按 `h = Z = 0` 处理。

形式化的主定理适用于任意域 `K`、任意 `K` 上的向量空间和任意有限坐标集；因此包括原文的有限域、任意有限斜率维数情形。
`minimumCost` 使用自然数下确界，其等式定理明确要求初始总和为零；不对不满足该条件的输入解释这个自然数值。

| 结论 | Lean 声明 |
|---|---|
| 所有合法成功方案都至少需要 h − Z 次 | `HZ.cost_lower_bound` |
| 存在恰好使用 h − Z 次的合法方案 | `HZ.cost_attained` |
| 最小代价的等式 | `HZ.minimumCost_eq` |
| 原文锚定、完整参数族的主子式最优代价 | `HZ.anchored_guard_optimal` |
| 五元素域中两个例子的最优次数为 2、3 | `HZ.Examples.paired_minimum`、`HZ.Examples.indivisible_minimum` |

## 证明如何覆盖关键条件

下界从一个已完成的操作序列向前追溯。终点的每个单坐标都是零和组。反向跨过一次行加法时，合并两个受影响坐标所在的组即可，组数最多减少一。
免费置换只搬移标识，非零缩放不改变各坐标的向量值。这个过程覆盖全部初始坐标。
随后证明：移除初始零坐标时，分组数最多按移除的坐标数减少，因而准确得到非零坐标定义下的 `h − Z` 下界。

达到下界的构造选取一个组数最大的零和划分。在每组中保留一个 `uⱼ ≠ 0` 的坐标，依次使用系数 `−uᵢ/uⱼ` 消去其余坐标。
Lean 证明系数非零、每步可逆、保留坐标的 `uⱼ` 不变，以及向量值确实整体转移。每组最后的值为该组的初始总和，因此归零。
不同组互不影响，总次数为各组“大小减一”之和，即 `h − Z`。最优划分的存在由有限性证明；这里没有声称寻找它可以在一般情形下高效完成。

## 与原主子式问题的连接

`HZ.Guards` 使用实际矩阵 `I − u v` 的主子式，参数行是完整族
`v = b + Σ_d a_d w_d`。它证明以下连接，而非把这些连接作为假设：

1. 主子式等于一减去对应坐标上的 `uᵢ vᵢ` 之和。
2. 对完整参数族，所有真前缀主子式通过且总斜率为零，必然使每个坐标的斜率向量值为零。
3. 若 `b` 只支撑在一个坐标 `c`，`u_c b_c = 1`，且该处斜率列为零，则上述构造保留 `b`。
   追加一次免费置换，把 `c` 放在最后，所有受检真前缀主子式均等于一。

因此，在这些锚定及完整参数族条件下，`h − Z` 也是原主子式问题的精确最小代价。
完整行列式不属于受检对象；空前缀的行列式为一，不影响结论。

## 文件入口

| 文件 | 内容 |
|---|---|
| [`HZ/Partitions.lean`](HZ/Partitions.lean) | 有限分区、合并、置换、移除零坐标及最大零和组数 |
| [`HZ/Operations.lean`](HZ/Operations.lean) | 合法操作、准确计费、逆操作和单步消元 |
| [`HZ/Construction.lean`](HZ/Construction.lean) | 单组及多组的达到下界构造、载体保持 |
| [`HZ/Optimality.lean`](HZ/Optimality.lean) | 一般下界、达到下界、最小代价等式 |
| [`HZ/Guards.lean`](HZ/Guards.lean) | 实际主子式、完整参数族必要性及锚定最优性 |
| [`HZ/Examples.lean`](HZ/Examples.lean) | 原文五元素域实例的确切最优值与实际操作序列 |
| [`Audit.lean`](Audit.lean) | 22 个关键声明的传递公理依赖和主定理签名 |
| [`verify.ps1`](verify.ps1) | 编译、来源扫描、公理检查和完整内核重放入口 |
| [`verification/RESULT.json`](verification/RESULT.json) | 验证结果、耗时和被验证文件的 SHA-256 |

## 复现

安装 [elan](https://github.com/leanprover/elan) 和 PowerShell 7。
在本目录执行下列命令。`lean-toolchain` 固定 Lean 4.24.0；`lake-manifest.json` 固定 mathlib 及其间接依赖。
首次取得工具和依赖需要联网。

```text
pwsh -NoProfile -File ./prepare.ps1
git clone --branch v4.24.0 https://github.com/leanprover/lean4checker.git .verification-tools/lean4checker
git -C .verification-tools/lean4checker checkout --detach da26eb05e9959402afcb9bd6dfe5dc4f700f70d6
lake -d .verification-tools/lean4checker build lean4checker
pwsh -NoProfile -File ./verify.ps1 -CheckerExe ./.verification-tools/lean4checker/.lake/build/bin/lean4checker
```

Windows 上给最后的检查器路径加 `.exe`。已有独立 Lean 工具目录时，可用 `-LeanBin` 指定；脚本默认从 `PATH` 查找工具。
新日志保存在 `.verification-runs/`，不覆盖 `verification/` 中保存的验证证据。
完整重放包括 `ProofCheck` 的导入依赖，可能耗时数分钟。

也可以只执行编译和公理输出：

```text
lake build
lake env lean -DwarningAsError=true Audit.lean
```

编译把警告视为错误。项目证明不使用证明占位符、新增公理、`native_decide` 或跳过内核检查的设置。
22 个关键声明的传递公理依赖按白名单检查，只允许 `propext`、`Classical.choice`、`Quot.sound`。
例子中的 `decide` 由 Lean 内核归约，不依赖本机编译器产生的真假判断。
官方 lean4checker 使用相同的 Lean 内核；新环境重放不等于采用另一种独立实现的内核。

## 范围与署名

本次涵盖一般斜率分离定理及锚定完整参数族推论。不涵盖原项目的二元虚拟坐标公式、三元域代价包络、轨道计数、复杂度归约或动态规划复杂度。
这些操作次数也不等于实际调用者的物理成本，不改变整数乘法复杂度指数。

形式化由 SHIN09-git 的研究项目使用 OpenAI Codex 完成；原证明及其前人来源保留在 `reference/NOTICE`。
零和分组原理、行操作及行列式恒等式的既有贡献不因形式化而变成新发现。
原文与 Lean 定义的对应关系由本次 AI 辅助工作核对，未宣称外部人工审核或上游科学验收已经完成。
本项目采用 Apache-2.0；下载的 Lean、mathlib 和检查器保留各自许可，源码及编译缓存不包含在轻量归档中。
