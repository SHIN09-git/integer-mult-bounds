# Monomial guard Lean proof suite

本分支收录 $h-Z$ 最优性、三元域代价界、虚拟项最优性，以及生成最优行操作的标签动态规划和计数向量动态规划。压缩算法的 Lean 项目引用相邻的标签算法目录。

| 证明包 | 已验证结论 | 公理检查 | 内核重放 |
|---|---|---:|---:|
| [三元域证明](../monomial-guard-ternary-lean/README.md) | $\max(S,L)\le C\le 2S+L$，任意非负参数的两端可达 | 40 条 | 527.860 秒 |
| [虚拟项与二元域证明](../monomial-guard-dummy-lean/README.md) | 非零目标的集中代价 $h-Z_*$，二元域归一化守卫族的精确代价 | 28 条 | 507.139 秒 |
| [动态规划与操作序列](../monomial-guard-dp-lean/README.md) | 算出 $Z$ 和 $Z_*$，生成最少行加法，并给出固定行序所需的免费换位 | 25 条 | 645.559 秒 |
| [按电荷类型压缩的动态规划](../monomial-guard-count-dp-lean/README.md) | 对每个子集证明 $P(S)=D(c(S))$，证明状态数乘积上界，并从类型分组恢复两种目标的最优真实行操作 | 32 条 | 612.213 秒 |
| [按步长填表的复杂度](../monomial-guard-stride-dp-lean/README.md) | 合法前驱读数与地址公式，逐格等于原表，恢复两类最优操作。填表时间 $O((1+t+d)N)$，表空间 $O((1+d)N)$ | 35 条 | 636.095 秒 |

最优性比较允许使用真实零电荷坐标，以及任意穿插的免费置换和非零缩放。虚拟标签只参与分组，生成的操作只使用真实行号。[原有 $h-Z$ 证明](../monomial-guard-hz-lean/README.md) · [验证收据索引](BUNDLE.json)

## 范围与来源

三元域定理要求完整仿射族及 $bu=1$、$Wu=0$。两端构造覆盖所有非负参数，允许维数变化，并保留一个零标量辅助坐标。一般域集中定理要求目标总和非零。二元域主子式结论要求守卫族非空且各行归一化，允许重复和相关的守卫。

动态规划对带标签的子集逐层查表。生成器返回每条行加法的两个行号和系数，Lean 对所返回序列证明合法性、终态和付费操作数。固定行序的两个入口还返回具体换位。[形式化入口](../monomial-guard-dp-lean/GuardDP/Solver.lean) · [固定行序](../monomial-guard-dp-lean/GuardDP/Guards.lean)

压缩算法按不同电荷的重数填表。只出现两种电荷、各有 20 个标签的样例使用 441 个表项，恢复 20 次最优行加法。增广表允许真实电荷与虚拟电荷同值，恢复时按标签身份分开。[逐项等价与状态数](../monomial-guard-count-dp-lean/CountDP/Score.lean) · [恢复证明](../monomial-guard-count-dp-lean/CountDP/Groups.lean)

按步长填表的程序扫描每个计数位，对正计数各读一次前驱，只对获胜前驱累加一次向量。两种电荷各有 20 个时共读 840 次前驱。复杂度从给定轴表起算，按机器字、坐标访问和标量运算计费。[实现与模型](../monomial-guard-stride-dp-lean/README.md) · [复杂度定理](../monomial-guard-stride-dp-lean/StrideDP/Asymptotics.lean)

数学来源固定于提交 `03caa7f6cb5bd21c834024e9d81f6b43eb325b91`，此前 $h-Z$ 形式化固定于 `b87752d0291dc8b1df46b9abbccdc739d7c5be57`。验证记录来自本地 Lean 编译、公理检查及官方检查器的新环境内核重放。各包保留署名与 Apache-2.0 许可，并披露 OpenAI Codex 的实质协助。[原研究 PR](https://github.com/CrocSwap/integer-mult-bounds/pull/6712)

## Open next questions

1. 给从原始标签到显式操作序列的全过程计费。可以先验证按类型建标签桶、回溯时每个真实标签恰好取出一次，再计入生成行加法系数的域运算。
2. 形式化一般三元输入的免费等价类及其最短路算法。起点是证明免费操作前后具有相同的最小付费代价。[相关三元域研究](https://github.com/CrocSwap/integer-mult-bounds/pull/6793)
