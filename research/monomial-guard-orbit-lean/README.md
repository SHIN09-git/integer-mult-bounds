# 一般三元守卫实例的精确最短路

给定有限行数、有限斜率维数的三元完整仿射族，若 $Wu=0$、$bu=1$，`solve` 返回一串可在输入上直接执行的行加法。Lean 证明其长度恰好为前序定理定义的最优付费次数 $C$。若要在给定行序下检查全部真前缀主子式，`solveFixed` 还返回最后一次免费置换。[求解器](OrbitGuard/Solver.lean) · [固定行序输出](OrbitGuard/Fixed.lean) · [原始代价定义](../monomial-guard-ternary-lean/Ternary/Envelope.lean)

## 免费操作与图上的边

完整状态 $s$ 的第 $i$ 行写作 $r_i=(u_i,w_i,b_i)$，其中 $w_i$ 是全部斜率坐标。每次行加法收费 1，行置换和各行独立的非零缩放免费。三元域的非零标量只有 $1,-1$，且均等于自身的逆。因此可以给每行记录无序集合 $\{r_i,-r_i\}$，再给整个状态记录这些集合的多重集。重复行各占一项，$u_i=0$ 的行也保留 $w_i,b_i$。两个状态的记录相等，当且仅当一个能通过一次行置换和一次逐行缩放变成另一个。[等价类及其完整性](OrbitGuard/Classes.lean)

图的顶点是实际状态的免费等价类。一次合法行加法在两类之间给出一条单位长度的有向边。算法每次只需要在一个代表上尝试行加法。设免费变换先按 $\pi$ 重排，再逐行乘以 $c_i$。若在变换后的行号上执行 $R_i\gets R_i+aR_j$，就能在原代表上执行 $R_{\pi(i)}\gets R_{\pi(i)}+(ac_j/c_i)R_{\pi(j)}$，到达同一终点类。[行加法换算与所有后继](OrbitGuard/Moves.lean)

对任意完整状态 $s,t$ 和自然数 $n$，Lean 证明

$$
[s]\;\text{到}\;[t]\;\text{有长为 }n\text{ 的路径}
\quad\Longleftrightarrow\quad
\text{原模型可从 }s\text{ 到达 }t\text{，恰用 }n\text{ 次付费行加法。}
$$

该对应允许免费操作穿插在任意位置，也覆盖 $n=0$。把含有成功代表的类作为终点集合，就得到起点到该集合的距离等于 $C(s)$。归一化条件保证终点可达且最小值能取到。这里的成功条件要求对完整仿射族的每个参数、每个真前缀，主子式都非零。[路径与执行的双向证明](OrbitGuard/Distance.lean) · [主子式判据](../monomial-guard-ternary-lean/Ternary/Guard.lean)

## 可执行的最短路

搜索从原始行号出发，按付费次数逐层展开。同一等价类首次出现时保留一个实际状态和到达它的行加法序列。每一层都覆盖最短距离等于该层深度的全部顶点。遇到成功状态后，返回的序列可直接在原始行上重放。成功测试检查每行电荷都为零，并检查标量电荷 $u_i b_i$ 中 $+1$ 与 $-1$ 的个数之差是否属于 $\{1,-2\}$。[逐层搜索的不变量](OrbitGuard/Layers.lean) · [返回值最优性](OrbitGuard/Solver.lean)

实现以 $2m+L(s)$ 为搜索深度上限，$m$ 为行数，$L$ 可由标量电荷直接计算。已证上界 $C\le 2S+L$ 和 $S\le m$ 保证这个上限足够。实际用时取决于搜索经过多少个状态类。`solveFixed` 还会枚举行置换，找出满足固定行序主子式条件的一个具体排列。这一步最多枚举 $m!$ 个排列。[固定行序求解器与证明](OrbitGuard/Fixed.lean)

## 五行样例

取一个斜率坐标，令 $u=(1,1,1,1,1)$、$w=(1,1,1,1,-1)$、$b=(1,1,1,1,0)$。从 0 开始编号，程序返回

$$
R_0\gets R_0+R_1,\qquad R_0\gets R_0+R_2,\qquad R_3\gets R_3-R_4.
$$

重放后，原行序已经通过全部参数的真前缀主子式检查。也可以直接核对三步的下界。五个非零电荷最多分成两组，一组为 $(1,-1)$，另一组为 $(1,1,1)$，所以仅分离电荷就至少需要 $5-2=3$ 次行加法。[样例及独立主子式检查](OrbitGuard/Examples.lean) · [可执行输出](verification/examples.log) · [三元标量电荷的组数公式](../monomial-guard-small-fields-lean/README.md)

同一对代价指标也可能对应两个答案。仍取五行、$u$ 全为 1，固定 $w=(1,-1,0,0,0)$。若 $b=(0,0,1,0,0)$，程序返回 1 步。若 $b=(-1,-1,1,1,1)$，则返回 2 步。两个输入都只有一对待分离的相反电荷，初始标量差都为 1，所以同为 $S=1,L=0$。后一输入正是原研究中达到上端的五行例子。[原五行构造](../monomial-guard-ternary-lean/reference/GAP.md)

在 Lean 中可以直接复现这两个输入。

~~~lean
import OrbitGuard.Examples
open OrbitGuard OrbitGuard.Examples Ternary

def pencil (b : Fin 5 → F) : State (Fin 5) (Fin 1) :=
  oneSlope (fun _ => 1) ![1,-1,0,0,0] b

#eval (solve (pencil ![0,0,1,0,0])).map List.length       -- some 1
#eval (solve (pencil ![-1,-1,1,1,1])).map List.length     -- some 2
~~~

## 复现与验证

在同一提交下相邻检出本包和 `monomial-guard-ternary-lean`，使用固定的 Lean 4.24.0。在本目录执行

~~~powershell
./prepare.ps1
lake build OrbitProofCheck
lake env lean Examples.lean
~~~

完整验证使用与该 Lean 版本匹配的官方 `lean4checker`。将其放入命令路径，或通过 `-CheckerExe` 指定位置，然后执行 `./verify.ps1`。脚本核对前序证明包的 27 个输入，检查 37 条声明的公理，并在新环境中重放整个导入链。[验证收据](verification/RESULT.json) · [公理记录](verification/axioms.log) · [文件摘要](SHA256SUMS)

8 组可执行检查覆盖 0 至 3 次最优行加法、需要免费交换才能通过的固定行序、隐藏斜率、重复行、零行和两个独立斜率坐标。两行且仅有一个斜率坐标时，共有 $3^6=729$ 个原始输入。程序对其中全部 72 个归一化输入逐一比较商图解与行号固定的直接搜索。直接搜索枚举两个最终行序和全部三个仿射参数，并用秩一矩阵的主子式公式检查每个真前缀。[交叉核对实现](OrbitGuard/Examples.lean) · [复现输出](verification/examples.log)

完整行按免费操作归类、单位代价边和广度优先搜索的数学方法均出自 SHIN09-git 的原研究。这里把任意长度的路径提升、逐层搜索和操作序列恢复形式化为 Lean 定理。三元模型与代价界沿用固定于提交 `03caa7f6cb5bd21c834024e9d81f6b43eb325b91` 的原研究及其前序 Lean 包。Nick Petalas 另给出了至多两次付费操作的电荷判据，相关版本为 `3ae29191befb4289cf4a187f685bce8d4f129cf8`。本包的任意距离证明使用完整行状态。[原轨道算法](https://github.com/SHIN09-git/integer-mult-bounds/blob/03caa7f6cb5bd21c834024e9d81f6b43eb325b91/research/monomial-guard-settlement/ORBITS.md) · [两步判据](https://github.com/CrocSwap/integer-mult-bounds/pull/6793) · [署名与许可](NOTICE)

## Open next questions

在三步及更远的搜索中，能否用更少的行数据保持最短距离，并从这些数据恢复最优操作？等价类判定只证明何时可用免费操作互达。不同的类仍可能具有相同的最优值。
