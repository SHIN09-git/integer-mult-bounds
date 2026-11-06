# 虚拟项不参与操作的 h − Z* 最优性定理

**2026-11-07：验证通过。** 编译、28 条关键声明的公理检查及包含全部导入依赖的新环境内核重放均已完成。重放耗时约 507 秒。详见 [验证摘要](verification/SUMMARY.json) 和 [原始结果](verification/RESULT.json)。

本项目证明：在任意域上，若有限组真实坐标的联合向量总和为非零 \(\tau\)，把这些值集中到一个真实坐标的最少付费行加法次数恰好等于 \(h-Z_*\)。额外虚拟项只用于定义 \(Z_*\) 和证明分组界，**从未进入可操作的状态或行操作序列**。

随后证明二元域任意非空、归一化守卫族的精确主子式代价也是 \(h-Z_*\)。原文来自 [PR #6712](https://github.com/CrocSwap/integer-mult-bounds/pull/6712)，固定在提交 03caa7f6cb5bd21c834024e9d81f6b43eb325b91 的 “Arbitrary binary families” 一节。副本见 [reference/PROOF.md](reference/PROOF.md)。

## 一般域的集中定理

设 \(I\) 为有限真实坐标集，\(K\) 为任意域，\(V\) 为 \(K\) 上的向量空间。状态包含 \(u_i\in K\)、\(w_i\in V\) 以及随操作更新的附加标量行 \(b_i\)。定义
\[
y_i=u_iw_i,\qquad \sum_i y_i=\tau\ne0.
\]

\(h\) 是初始 \(y_i\ne0\) 的真实坐标数。在这些带独立标识的非零项中，额外加入一个标识不同的 \(-\tau\)。\(Z_*\) 是把增广列表划分成非空零和组时的最大组数；相同向量值始终保留不同标识。

成功条件是存在真实坐标 \(c\in I\)，使最终 \(y_c=\tau\)，其他真实坐标全部为零。每次合法行加法
\[
u_i\leftarrow u_i+a u_j,\quad
w_j\leftarrow w_j-a w_i,\quad
b_j\leftarrow b_j-a b_i
\]
计一次，要求 \(i\ne j,a\ne0\)。置换及非零对角缩放免费，可以任意穿插。所有初始真实零坐标均保留，允许被任意竞争方案使用。

物理状态和序列始终是 <code>HZ.State I K V</code> 与 <code>HZ.Run</code>，坐标类型只有 \(I\)。记账函数 <code>Dummy.augment</code> 则使用 <code>Option I</code>：<code>none</code> 表示虚拟项，<code>some i</code> 表示真实标识。<code>Dummy.minimumCost</code> 只在真实状态和真实序列上取最小值。因此虚拟项从类型上就不属于操作空间。

## 下界与达到下界的构造

下界沿任意真实操作序列反向追溯。在成功终点，把唯一的非零真实坐标与虚拟项放在同一组，其余真实坐标各自成组。每组的增广总和都是零。反向跨过一次行加法时，至多合并两个真实坐标所在的组；免费置换固定虚拟标识，缩放保持联合向量值。最后移除初始真实零坐标，得到 \(h-Z_*\) 下界。这覆盖所有真实零坐标辅助和所有合法操作次序。

上界选取一个达到 \(Z_*\) 的增广零和分区。由于 \(\tau\ne0\)，虚拟项不能单独成组。删除虚拟标识后，每个组仍非空，组数保持为 \(Z_*\)，全部真实非零坐标仍被恰好覆盖一次。

恰有一个真实组的总和为 \(\tau\)，其余组总和为零。对每组选择一个 \(u_j\ne0\) 的真实累积坐标，使用已验证的合法消元构造，把其他坐标的值移到该处。每个大小为 \(k\) 的组使用 \(k-1\) 次，合计
\[
\sum_B(|B|-1)=h-Z_*.
\]
非目标组归零，目标组留下 \(\tau\)。整个构造只调用真实坐标上的行加法。

## 二元域任意守卫族

令 \(R\) 为非空守卫索引集，\(K=\mathbb F_2\)。在 <code>Binary</code> 模块中，\(w_i(r)\) 表示第 \(r\) 个守卫行在坐标 \(i\) 的系数；这里的 \(w\) 堆叠全部守卫行，而非三元域完整仿射族中的斜率参数。

归一化条件为
\[
\forall r\in R,\quad\sum_i u_iw_i(r)=1.
\]
因此联合向量 \(z_i=(u_iw_i(r))_{r\in R}\) 的总和为全一向量 \(\mathbf1\ne0\)。不要求守卫行独立，也不要求它们形成完整仿射族；重复和依赖的行均被包含。Lean 不需要 \(R\) 有限，因此覆盖任意非空有限列表。

每个守卫检查实际矩阵 \(I-u\,w(r)\) 的真前缀主子式。行列式公式给出
\[
\det=1-\sum_{\text{前缀 }i}u_iw_i(r).
\]
在二元域，行列式非零等价于前缀和为零。所有守卫同时通过，意味着每个真前缀的联合向量和为零。相邻前缀相减，得到所有非末尾坐标为零；归一化使最后一个坐标为 \(\mathbf1\)。

反过来，若联合向量已集中到一个真实坐标，把它免费置换到最后即可使所有真前缀主子式通过。故原问题的精确代价为 \(C_2=h-Z_*\)。

<code>Binary.fullguard_run_iff</code> 证明免费选择最终顺序与原始固定顺序具有相同的付费可达性；<code>Binary.fixed_order_optimal</code> 直接给出固定顺序问题的下界与达到下界序列。完整行列式不参与检查。

空守卫族明确排除；其全一向量等于零，不能套用非零目标定理。一般域集中定理同样明确要求 \(\tau\ne0\)。

## 定理入口

| 结论 | Lean 声明 |
|---|---|
| 删除虚拟项后组数、非空性、覆盖与各组总和 | Dummy.real_parts |
| 任意真实序列的反向分区证书 | Dummy.execution_partition |
| 一般域下界 | Dummy.cost_lower_bound |
| 只操作真实坐标的达到下界构造 | Dummy.cost_attained |
| 一般域最小代价等式 | Dummy.minimumCost_eq |
| 下界与构造的合并声明 | Dummy.optimal_cost_eq_h_sub_Zstar |
| 二元域实际主子矩阵行列式连接 | Binary.principalMinor_submatrix |
| 主子式通过与集中条件等价，允许免费排序 | Binary.fullguard_iff |
| 二元域精确最小代价 | Binary.cost_eq_h_sub_Zstar |
| 原始固定顺序的最优性 | Binary.fixed_order_optimal |

四个 <code>Dummy/</code> 模块依次处理增广分区、下界、真实构造和最小值等式；两个 <code>Binary/</code> 模块处理主子式连接和精确代价。<code>HZ/</code> 六个模块及根入口 <code>HZ.lean</code> 沿用此前验证版本，七个文件的字节保持不变。

## 复现与验证证据

需要 Lean 4.24.0 和 PowerShell 7。<code>lean-toolchain</code> 固定 Lean 版本，<code>lake-manifest.json</code> 固定 mathlib 及间接依赖。可安装 [elan](https://github.com/leanprover/elan) 管理 Lean；首次取得依赖需要联网。

~~~text
pwsh -NoProfile -File ./prepare.ps1
git clone --branch v4.24.0 https://github.com/leanprover/lean4checker.git .verification-tools/lean4checker
git -C .verification-tools/lean4checker checkout --detach da26eb05e9959402afcb9bd6dfe5dc4f700f70d6
lake -d .verification-tools/lean4checker build lean4checker
pwsh -NoProfile -File ./verify.ps1 -CheckerExe ./.verification-tools/lean4checker/.lake/build/bin/lean4checker
~~~

Windows 上为检查器路径补上 <code>.exe</code>。已有独立 Lean 安装时可传入 <code>-LeanBin</code>。新记录写入 <code>.verification-runs/</code>，不覆盖随包保留的 <code>verification/</code> 证据。

只编译和查看公理依赖：

~~~text
lake build
lake env lean -DwarningAsError=true Audit.lean
~~~

验证脚本检查七个继承源文件、源码禁用项、将警告视为错误的编译、28 条关键声明的传递公理白名单，以及 <code>DummyProofCheck</code> 和全部导入依赖的新环境内核重放。还会核对输入在整个运行期间保持不变，全部成功后才写出 PASS 收据。

只允许 Lean 标准公理 <code>propext</code>、<code>Classical.choice</code>、<code>Quot.sound</code>。项目不使用证明占位符、新增公理、<code>native_decide</code> 或跳过内核的设置。普通 <code>decide</code> 由内核归约。官方检查器使用同一个 Lean 内核实现，不是另一套独立内核。

## 范围、署名与后续问题

一般集中定理对任意域和向量空间成立；完整主子式代价等式在二元域成立。这里没有声称同一必要性结论适用于任意奇数域，也没有证明实际乘法调用者的物理成本或新的整数乘法复杂度指数。

原研究和前人来源保留在 [reference/NOTICE](reference/NOTICE)，本次来源与边界见 [reference/DUMMY-SOURCE.json](reference/DUMMY-SOURCE.json)。形式化由 SHIN09-git 的研究项目使用 OpenAI Codex 完成，采用 Apache-2.0。文字与 Lean 模型的对应关系由本次 AI 辅助核对，未宣称外部人工审核或上游科学验收已完成。

Open next questions:

1. 形式化计算最大零和分组数的动态规划，证明输出分区达到 \(Z_*\)。当前证明给出数学存在性，没有高效求解承诺。
2. 把达到下界构造接到可执行证书生成器，返回真实坐标上的具体系数序列。
3. 在一般三元输入上形式化免费等价类和最短路算法，验证逐实例精确代价及固定维数断言。

归档只含源码、引用材料和验证证据，不含 Lean 二进制或 mathlib 缓存。

