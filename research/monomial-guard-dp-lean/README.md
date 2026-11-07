# 用动态规划计算 Z、Z* 并还原最优行操作

给定带标签的电荷，Lean 程序返回具体分组和逐条可执行的行加法。每条行加法给出目标行、来源行和域系数。把指令作用于原始状态后，Lean 证明终态满足目标，并把实际指令数与任意合法执行的代价比较。

| 输入与目标 | 计算分组的结论 | 返回的行加法 |
|---|---|---|
| 真实电荷之和为零，每个坐标的最终电荷都为零 | `computes_Z` 证明组数等于 $Z$ | `separationWord_optimal` 证明恰用 $h-Z$ 次 |
| 真实电荷之和为 $\tau\ne0$，末态由一个真实坐标承载 $\tau$ | `computes_Zstar` 证明增广后的组数等于 $Z_*$ | `concentrationWord_optimal` 证明恰用 $h-Z_*$ 次 |

这里 $h$ 只数电荷非零的真实坐标。一般定理允许任意域以及该域上模中的向量电荷。可执行入口使用有限、有序的真实标签，并要求可以判定电荷是否相等。对于带锚点的完整仿射守卫族，以及二元域上非空的归一化守卫族，程序另给出将承载行移到末位的真实换位。Lean 证明换位后的固定行序通过所有受检主子式，付费操作数仍然最少。[组数定理](GuardDP/Labels.lean) · [最优操作定理](GuardDP/Solver.lean) · [固定行序定理](GuardDP/Guards.lean)

## 子集递推与分组还原

对非空标签集 $S$，程序在前一层共享表中比较各个 $S\setminus\{i\}$ 的结果。空集得零分，其余子集满足

$$
P(S) = \mathbf{1}_{\sum_{i\in S}y_i=0}
       + \max_{i\in S} P(S\setminus\{i\}).
$$

每个表项保存胜出前驱已经封闭的组。当 $S$ 的总和为零时，把尚未分配的标签封闭成一个新组。同分时取输入顺序中的第一个候选。Lean 证明，对任意子集，已有组的个数是其中互不相交的非空零和组能达到的最大值。总和为零时，这些组恰好覆盖整个子集，因此组数等于原有形式化中对全部合法分组定义的最大值。[查表与递推](GuardDP/Table.lean) · [递推等式](GuardDP/Recurrence.lean) · [最优性证明](GuardDP/Correctness.lean)

在非零目标问题中，程序仅在分组时加入一个电荷为 $-\tau$ 的虚拟标签。删去该标签后，每组仍含真实坐标，恰有一组的真实电荷和为 $\tau$。每个真实组以最小行号 $j$ 为承载行，让其他行 $i$ 依次执行 $R_i\gets R_i-(u_i/u_j)R_j$。程序根据当前状态生成系数。Lean 验证每步所用行号不同、系数非零，并在同时更新两条对偶行后证明终态正确。最短性比较允许其他执行免费置换、非零缩放及使用零电荷辅助坐标。[行指令与解释器](GuardDP/Word.lean) · [整组执行证明](GuardDP/Family.lean)

## 运行例子

在 $\mathbb F_5$ 上取电荷 $(1,1,1,2,4,4,4,3)$，且各 $u_i=1$。程序按从 0 开始的行号返回四组 $\{0,4\},\{1,5\},\{2,6\},\{3,7\}$。对应指令依次把第 0、1、2、3 行的 4 倍加到第 4、5、6、7 行，最终所有电荷为零。最短长度为 $8-4=4$。

另外四项回放覆盖一般非零目标、两个二元守卫与末位换位、空输入和仅有一个真实承载行的情形。五项检查均可重新运行。[输入与断言](GuardDP/Examples.lean) · [实际输出](verification/examples.log)

## 复现验证

使用 `lean-toolchain` 指定的 Lean 4.24.0 和 `lake-manifest.json` 固定的依赖。在本目录中执行下列命令。

~~~powershell
./prepare.ps1
lake build DPProofCheck
lake env lean Examples.lean
~~~

完整检查另需与该 Lean 版本匹配的官方 `lean4checker`。将其放在可执行文件搜索路径中，然后运行以下脚本。也可用 `-LeanBin` 和 `-CheckerExe` 指定两个工具的位置。

~~~powershell
./verify.ps1
~~~

脚本核对依赖版本与 15 份沿用源码，编译整个项目，运行五项例子，检查 25 条定理的传递公理依赖，并用官方检查器在新环境中重放根模块及全部导入。每次运行的收据写入 `.verification-runs/`。本次发布附有输入哈希、日志及内核重放结果。[验证收据](verification/RESULT.json) · [公理检查](verification/axioms.log) · [内核日志](verification/kernel-replay.log)

## 来源与后续问题

数学依据为原研究提交 `03caa7f6cb5bd21c834024e9d81f6b43eb325b91` 中的子集递推和分组行操作构造。操作模型和既有下界沿用已经验证的 `HZ`、`Dummy` 和 `Binary` 模块。原作者及早期工作的署名见随附 NOTICE。[原始算法](reference/ALGORITHM.md) · [原研究 PR](https://github.com/CrocSwap/integer-mult-bounds/pull/6712) · [署名](NOTICE)

### Open next questions

本次实现按标签区分子集，证明覆盖数值、分组和操作序列。原文还给出了复杂度估计及按电荷类型压缩的算法。可先证明同一类型内交换标签保持各表项得分，再验证压缩后的前驱能还原出互不重复的真实行号。具体运行时间和空间界需要为查表、求和及保留分组分别计费，尚未形式化。
