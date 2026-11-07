# 按电荷类型压缩的动态规划

本包实现计数向量动态规划，返回最优组数、只含电荷类型的分组，以及可在原始行状态上逐条执行的最优操作序列。它使用相邻目录中的标签动态规划作为数学规格。计算表格和恢复行号是两个独立入口。

## 已证明的结论

令 $U$ 为输入标签集，$v_j$ 为其中实际出现的不同电荷，$n_j$ 为 $v_j$ 的总重数。对于任意 $S\subseteq U$，$c_j(S)$ 是 $S$ 中电荷为 $v_j$ 的标签数，$P(S)$ 是原标签算法的得分。

| 定理 | 结论 |
|---|---|
| `P_eq_D`、`layer_score_eq_D` | $P(S)=D(c(S))$ 对所有子集成立，包括总电荷非零的中间状态，也适用于查询已填好的标签表。 |
| `state_count`、`reachable_state_bound` | 新算法实际分配的数组恰有 $\prod_j(n_j+1)$ 格。所有标签子集产生的不同计数向量数至多为该乘积。空输入分配一格。 |
| `compressed_certificate` | 总电荷为零时，按类型生成的分组一定能恢复。每个输入标签恰好使用一次。每个真实组映回电荷后，逐组保留原电荷及重数，组数达到全局最大值。 |
| `score_Z`、`separationWord_optimal` | 真实总电荷为零时，只求值得到 $Z$。恢复的序列用 $h-Z$ 次付费行加法消去所有电荷，任何合法成功执行至少付出这个代价。 |
| `score_Zstar`、`concentrationWord_optimal` | 真实总电荷为 $\tau\ne0$ 时，增广计数表给出 $Z_*$。恢复的序列用 $h-Z_*$ 次真实行加法，把 $\tau$ 集中到一个真实坐标，此代价最小。 |

$h$ 是非零真实电荷数。增广问题的 $n_j$ 包括电荷为 $-\tau$ 的一个虚拟标签。若真实标签也有该电荷，两者在同一个计数位中累加。恢复标签后按身份删除虚拟项，每条行操作的输入类型只允许真实行号。定理比较的执行允许真实辅助行、免费置换和非零缩放。[得分与状态数](CountDP/Score.lean) · [两种组数与分组证书](CountDP/Groups.lean) · [操作最优性](CountDP/Operations.lean)

## 表格和回溯

第 $j$ 个计数位的取值为 $0,\ldots,n_j$。程序用混合进位制把计数向量编码成数组下标，从小到大填表。Lean 证明有效向量可由下标解回，且减去任一种现有电荷都得到更小的下标。因此每个表项只读已经填好的前驱。其得分为

$$
D(0)=0,\qquad
D(c)=\mathbf 1_{\sum_j c_j v_j=0}+\max_{j:c_j>0}D(c-e_j)\quad(c\ne0).
$$

若标签 $i$ 的电荷是 $v_j$，删去它就把 $c(S)$ 变为 $c(S)-e_j$。同一电荷类型的所有可删标签都进入同一个前驱，而每个正计数位至少对应一个可删标签。两边取最大值的候选得分相同，再按子集大小归纳便得到逐项等式。

每格只保存得分、选中的前驱电荷类型和一个零和分组标记。`solveCounts` 沿前驱生成只含电荷类型的组。`restoreGroups?` 可以直接读这些组，从仍可用的标签中选取同电荷的行号。它在恢复时区分每一次出现，即使电荷相同，真实行的系数也按各自当前状态计算。`fullScore` 提供只求值的入口。[混合进位编码](CountDP/Address.lean) · [表格](CountDP/Table.lean) · [类型分组](CountDP/Trace.lean) · [行号恢复](CountDP/Restore.lean)

带锚点的完整仿射守卫族和二元域上的非空归一化守卫族另有固定行序入口。它们返回所需的具体免费换位，并证明最终主子式通过、付费代价最小。真实行标签采用有限线性序，电荷需有可判定的相等关系。只含计数的表格不要求电荷类型本身可排序。[固定行序定理](CountDP/FixedOrder.lean)

## 可执行回放

| 输入 | 检查内容 |
|---|---|
| $\mathbb F_5$ 上的 $(1,1,1,2,4,4,4,3)$ | 64 个表项，逐一对照全部 256 个标签子集的得分。恢复四组，执行四次行加法，所有电荷归零。 |
| 真实电荷 $(2,4,2,3,0)$，目标为 $1\in\mathbb F_5$ | 真实标签和虚拟标签都有电荷 4，两者占用同一计数位。18 个表项，恢复两组，用两次行加法达到单行承载目标。 |
| 各 20 个 $1$ 和 $-1$，共 40 个真实标签 | 441 个表项，恢复 20 组，用 20 次行加法归零。 |
| 两条二元守卫、空输入、单一真实承载行 | 分别回放固定行序的免费换位、唯一的空状态，以及零次付费操作的非零目标。 |

[样例输入与断言](CountDP/Examples.lean) · [运行输出](verification/examples.log)

## 复现

检出本分支，保留本目录及相邻的 `../monomial-guard-dp-lean`。使用 `lean-toolchain` 固定的 Lean 4.24.0。在本目录运行以下命令。

~~~powershell
./prepare.ps1
lake build CountProofCheck
lake env lean Examples.lean
~~~

完整验证另需同版本的官方 `lean4checker`。将其放到可执行文件搜索路径中后运行 `./verify.ps1`，也可用 `-LeanBin` 和 `-CheckerExe` 指定工具位置。脚本核对前一份证明的 37 个输入及依赖版本，编译、执行样例并核查 32 条声明的传递公理，最后用官方检查器在新环境内重放整个导入链。[本次收据](verification/RESULT.json) · [公理检查](verification/axioms.log) · [内核重放](verification/kernel-replay.log) · [前一份证明](../monomial-guard-dp-lean/README.md)

## 来源

计数递推沿用固定提交 `03caa7f6cb5bd21c834024e9d81f6b43eb325b91` 的 `frequency_blocks`。标签表、操作模型和下界沿用提交 `549eaad16d52b48982c34b4b707fc33ce40b2111` 的证明包。数学署名和 Apache-2.0 许可随包保留。[原算法说明](../monomial-guard-dp-lean/reference/ALGORITHM.md) · [原实现](https://github.com/SHIN09-git/integer-mult-bounds/blob/03caa7f6cb5bd21c834024e9d81f6b43eb325b91/research/monomial-guard-settlement/algorithms.py#L6) · [署名](NOTICE)

## Open next questions

状态数已经精确计数。要给运行时间和总空间建立上界，下一步可分别计费地址编解码、查找最佳前驱、求和与回溯。当前实现以多重集表示重数，操作成本会受电荷表示和相等判定成本影响。
