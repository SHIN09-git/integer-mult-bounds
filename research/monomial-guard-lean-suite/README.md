# Monomial guard Lean proof suite

本分支收录 $h-Z$ 最优性、三元域代价界、虚拟项最优性，以及计算最优分组和操作序列的动态规划。各目录是独立 Lean 项目，附有固定依赖和复现说明。

| 证明包 | 已验证结论 | 公理检查 | 内核重放 |
|---|---|---:|---:|
| [三元域证明](../monomial-guard-ternary-lean/README.md) | $\max(S,L)\le C\le 2S+L$，任意非负参数的两端可达 | 40 条 | 527.860 秒 |
| [虚拟项与二元域证明](../monomial-guard-dummy-lean/README.md) | 非零目标的集中代价 $h-Z_*$，二元域归一化守卫族的精确代价 | 28 条 | 507.139 秒 |
| [动态规划与操作序列](../monomial-guard-dp-lean/README.md) | 算出 $Z$ 和 $Z_*$，生成最少行加法，并给出固定行序所需的免费换位 | 25 条 | 645.559 秒 |

最优性比较允许使用真实零电荷坐标，以及任意穿插的免费置换和非零缩放。虚拟标签只参与分组，生成的操作只使用真实行号。[原有 $h-Z$ 证明](../monomial-guard-hz-lean/README.md) · [验证收据索引](BUNDLE.json)

## 范围与来源

三元域定理要求完整仿射族及 $bu=1$、$Wu=0$。两端构造覆盖所有非负参数，允许维数变化，并保留一个零标量辅助坐标。一般域集中定理要求目标总和非零。二元域主子式结论要求守卫族非空且各行归一化，允许重复和相关的守卫。

动态规划对带标签的子集逐层查表。生成器返回每条行加法的两个行号和系数，Lean 对所返回序列证明合法性、终态和付费操作数。固定行序的两个入口还返回具体换位。[形式化入口](../monomial-guard-dp-lean/GuardDP/Solver.lean) · [固定行序](../monomial-guard-dp-lean/GuardDP/Guards.lean)

数学来源固定于提交 `03caa7f6cb5bd21c834024e9d81f6b43eb325b91`，此前 $h-Z$ 形式化固定于 `b87752d0291dc8b1df46b9abbccdc739d7c5be57`。验证记录来自本地 Lean 编译、公理检查及官方检查器的新环境内核重放。各包保留署名与 Apache-2.0 许可，并披露 OpenAI Codex 的实质协助。[原研究 PR](https://github.com/CrocSwap/integer-mult-bounds/pull/6712)

## Open next questions

1. 形式化按电荷类型压缩的动态规划。先证明同类型标签的置换保持得分，再构造恢复真实标签的算法并证明每个标签恰好使用一次。
2. 形式化一般三元输入的免费等价类及其最短路算法。起点是证明免费操作前后具有相同的最小付费代价。[相关三元域研究](https://github.com/CrocSwap/integer-mult-bounds/pull/6793)
