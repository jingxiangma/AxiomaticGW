# `AxiomaticGWTest/Basic.lean` 完整阅读说明

本文说明 `AxiomaticGWTest/Basic.lean` 的实际用途、直接和传递导入、每一组声明的验证内容、smoke test 与数学/API 回归测试的区别，以及它与专门测试文件的分工。

`Basic.lean` 在本次审查中只被读取和编译，没有修改。

## 1. 当前用途和文件性质

文件开头是：

```lean
module

import AxiomaticGW

/-!
# API regression tests

These examples check that the public import and local-instance interfaces work
as intended. They are deliberately kept outside the production library.
-/
```

因此它同时具有两种用途：

1. 顶层公共导入的 smoke test；
2. 跨多个模块的 API 和数学回归测试集合。

它不是纯粹的示例文件，因为里面的 `example` 明确锁定了公共 theorem、计算公式和跨层转换行为。它也不是唯一测试入口。

`lakefile.toml` 中有：

```toml
testDriver = "AxiomaticGWTest"

[[lean_lib]]
name = "AxiomaticGWTest"
globs = ["AxiomaticGWTest.+"]
```

所以 `Basic.lean` 是 `AxiomaticGWTest` 测试库中的一个模块。`lake test` 会构建该测试库中的测试模块；新建的专门测试文件也会被纳入，而不是由 `Basic.lean` 单独充当入口。

## 2. import 的作用

`Basic.lean` 只有一个直接 import：

```lean
import AxiomaticGW
```

它没有逐个直接导入 Linear、Frobenius、TFT 或 CohFT 模块。顶层 `AxiomaticGW.lean` 再公共导入：

- `AxiomaticGW.Frobenius.Examples`；
- `AxiomaticGW.CohFT.Ancestors`；
- `AxiomaticGW.CohFT.Classification`；
- `AxiomaticGW.Combinatorics.StableGraph`；
- `AxiomaticGW.GW.Constant`；
- `AxiomaticGW.GW.BigQuantumProduct`；
- `AxiomaticGW.GW.Descendants.FullPotential`；
- `AxiomaticGW.GW.Descendants.Stabilization`；
- `AxiomaticGW.GW.Descendants.Equations`；
- `AxiomaticGW.Geometry.VirtualGWPackage`；
- `AxiomaticGW.Linear.Contraction`；
- `AxiomaticGW.PointTarget.Descendants`；
- `AxiomaticGW.TFT.Correlator`；
- `AxiomaticGW.TFT.Classification`；
- `AxiomaticGW.TFT.Examples`；
- `AxiomaticGW.TFT.Frobenius`；
- `AxiomaticGW.TFT.Sewing`；
- `AxiomaticGW.Tautological.BasicStrata`；
- `AxiomaticGW.Tautological.DecoratedStableGraph`；
- `AxiomaticGW.Tautological.Getzler`；
- `AxiomaticGW.Tautological.LowGenus`；
- `AxiomaticGW.Tautological.StrataAlgebra`；
- `AxiomaticGW.Tautological.StrataModule`；
- `AxiomaticGW.Tautological.StrataRealization`。

这些模块又有各自的传递依赖。例如：

```text
AxiomaticGW
  -> Linear.Contraction
      -> Linear.Copairing
          -> Linear.PerfectPairing
```

因此，仅仅成功导入 `AxiomaticGW`，就间接检查了很大一部分项目依赖图能够 elaboration 和构建。这是宽范围 smoke test，但不等于逐个定义已经经过数学验证。

## 3. 文件开头的 namespace 和 open

```lean
namespace AxiomaticGWTest

open AxiomaticGW TensorProduct
```

所有声明放在测试 namespace 中，避免污染生产库 namespace。`open AxiomaticGW TensorProduct` 只是缩短后续名称，不会创建新的数学结构或实例。

## 4. 按代码顺序逐段阅读

## 4.1 `namespace Contraction`

第一个 example 验证标量值 contraction 在剩余输入重标号下自然：

```lean
(P.selfContract f).domDomCongr e =
  P.selfContract
    (f.domDomCongr (Equiv.sumCongr e (Equiv.refl (Fin 2))))
```

它检查：

- `selfContract` 的公共 API 可用；
- `domDomCongr` 与 contraction 的约定一致；
- 两个被收缩的 `Fin 2` 输入保持原顺序；
- 抽象类型类参数能推导。

第二个 example 对任意目标模块 `W` 验证 `selfContractTarget` 使用相同重标号约定。

这两个例子是对 `Linear/Contraction.lean` 的直接 API 回归测试，不只是 smoke test。

## 4.2 `namespace CommFrobeniusAlgebra`

按顺序共有以下验证。

### 4.2.1 局部 coalgebra 实例

```lean
letI : Coalgebra R A := F.toCoalgebra
```

验证 canonical coalgebra 可以局部安装，且 mathlib 的 `Coalgebra.counit` 与 `F.counit` 一致。它检查局部实例接口，不要求全局选择一个 Frobenius 结构。

### 4.2.2 局部 cocommutativity 实例

同时安装：

```lean
letI : Coalgebra R A := F.toCoalgebra
letI : Coalgebra.IsCocomm R A := F.toIsCocomm
```

然后调用 `Coalgebra.comm_comul`，验证项目构造与 mathlib coalgebra API 兼容。

### 4.2.3 二阶乘积代数的 handle element

验证：

```lean
(AxiomaticGW.CommFrobeniusAlgebra.productAlgebra R).handleElement = 1
```

这是一个具体计算回归测试。

### 4.2.4 TFT 非分离粘合

验证 `F.toTwoDimensionalTFT.nonseparating` 可通过公开接口使用，并给出 genus 增加一的 sewing law。

### 4.2.5 TFT 分离粘合

验证 `pairContract` 将两个 correlator 按分离节点粘合为总亏格 correlator。

### 4.2.6 基环 correlator 的具体计算

验证基环例子在任意亏格、`Fin 3` 输入时等于输入乘积：

```lean
(baseRing R).correlator g (Fin 3) a = ∏ i, a i
```

### 4.2.7 空标记 correlator

验证无输入 correlator 是闭曲面配分函数：

```lean
F.counit (F.handleElement ^ g)
```

### 4.2.8 插入单位元

验证在一个新标记处插入代数单位元不会改变 correlator。

### 4.2.9 限制到稳定 arity

验证转换为 `TopologicalCohFT` 后，底层三点 correlator 保持不变。这一例使用 `rfl`，同时锁定转换定义的规范化方式。

### 4.2.10 提取三点乘法

验证从前向 TFT 理论提取出的 product 等于原始代数乘法。

### 4.2.11 `threePointFunction` 公共名称

验证公开名称 `threePointFunction` 与 `Fin 3` correlator 的 curried 形式一致，防止以后重命名或参数约定破坏调用者。

这些例子大多是真正的 API 或数学回归测试，而不是仅仅检查 import。

## 4.3 `namespace FullCohFT`

按顺序验证以下内容。

### 4.3.1 常数目标的 degree zero

验证 `constantDegree ℚ 0` 是顶子模，任意有理数属于它。

### 4.3.2 `forgetNonseparatingEquiv` 的具体置换

检查遗忘标记和两个节点标记如何循环，并确认原始标记保持不变。这是具体的标签约定回归测试。

### 4.3.3 遗忘映射与非分离粘合

验证 `forget_nonseparating` 的完整复合等式，包括必要的标签 transport。

### 4.3.4 左分量遗忘与分离粘合

验证 `forget_separating_left`，包括 tensor target 上左因子的映射和标签重排。

### 4.3.5 几何最高次数

验证稳定曲线抽象目标中，次数超过 `StableArity.dimension` 的元素为零。

### 4.3.6 pushforward 和 kappa

一个 conjunction example 同时验证：

- forgetful pushforward 杀掉 degree zero；
- kappa class 在重标号下自然；
- kappa class 具有次数 `m`。

### 4.3.7 标量拓扑 correlator 转为常数 CohFT 类

验证 `TopologicalCohFT.toConstantCohFT` 的 `omega` 与原标量 correlator 一致。

### 4.3.8 转换后的 relabel

验证 converted full CohFT 通过公共 API 暴露 relabelling law。

### 4.3.9 转换后的非分离粘合

验证 `selfContractTarget` 与常数目标的非分离 cohomology map 相容。

### 4.3.10 平坦单位插入

验证转换后插入 `T.unit` 等于 forget map 作用于原 correlator。

### 4.3.11 分离粘合

验证 tensor-valued full CohFT 的 separating law。

### 4.3.12 constant 转换往返

验证 `toConstantCohFT.toTopologicalCohFT` 保持所有标量 correlator。

### 4.3.13 一般 topological part 在常数目标上的特化

验证 generic degree-zero construction 在 constant target 上恢复原 topological theory。

### 4.3.14 genus-zero 乘法结合律

验证从 converted CohFT 提取的 genus-zero product 满足结合律。

### 4.3.15 Frobenius 分类重建

验证从 topological CohFT 提取 Frobenius algebra，再重建 topological CohFT，可以恢复任意稳定 genus 和有限 label type 的 correlator。

### 4.3.16 零次幂三点 ancestor

验证 constant target 上三点、所有 psi 幂为零的 ancestor 等于原 topological correlator。

## 4.4 `namespace GromovWittenTheory`

按顺序验证：

1. 一个具体 `GWOutputDegree` 数值关系，说明 descendant cotangent 次数可补偿 primary expected degree；
2. descendant、ancestor 和 boundary correction 具有相同修正总次数；
3. 自然数有效曲线类的 `(1,2)` 是 `3` 的合法 splitting；
4. beta-zero reference theory 恢复底层 CohFT 类；
5. 小量子乘法系数的结合律，由 coefficientwise gluing 和 WDVV 得到；
6. 大量子乘法在零 primary background 特化为小量子乘法；
7. 大量子乘法在任意 primary background 交换。

数值 splitting 和 beta-zero 例子包含具体计算，其余主要是公开定理可调用性的 API 回归。

## 4.5 `namespace StableGraphs`

### 4.5.1 `loopGraph` fixture

定义一个单顶点、单环、一个 leg、顶点 genus 为零的稳定图。定义本身主要是测试 fixture。

随后两个 examples 验证：

1. 环贡献一个第一 Betti 数，因此 `totalGenus = 1`；
2. 唯一顶点满足 `StableArity`。

### 4.5.2 `twoLoopGraph` fixture

定义一个单顶点、两个不同 loop edge、没有 leg 的稳定图。

随后验证：

1. 任意两个完整 `ContractionOrder` 的边列表互为排列；
2. constant stable-curve target 给出的 ordered pullback 与 contraction order 无关。

fixture 定义本身不是断言；后续等式和性质 examples 才是回归测试。

## 4.6 `namespace HigherAndUnstableExtensions`

按顺序验证：

1. 一般 primary background 上的 genus-zero WDVV 给出 state-valued 大量子乘法结合系数相等；
2. 全局 string equation 将稳定 law 与 exceptional unstable convention 结合；
3. `positiveTailSplittings` 排除尾分量上的零曲线类。

## 4.7 `namespace PointTarget`

按顺序验证：

1. 点目标的零维交数在 `Mbar(0,3)` 上归一化为 `1`；
2. `Mbar(0,4)` 上 degree-zero integrand 因次数不匹配而给出 `0`；
3. DVV 归一化使用 `(2 * 1 + 1)!! = 3`。

这些是具体数学回归测试，不只是 API smoke test。

## 4.8 `namespace CompletedCoefficients`

按顺序验证：

1. Novikov 单项式相乘时曲线类相加、系数相乘；
2. Laurent 总自由能可以取回指定 genus coefficient；
3. 不同变量的形式偏导交换；
4. completed multivariable power series 的偏导满足乘积法则；
5. 重复变量在 potential profile 中贡献相应 factorial。

## 5. 哪些是 smoke test，哪些是真正回归测试

### 5.1 Smoke test

以下行为主要属于 smoke test：

- `import AxiomaticGW` 成功；
- 顶层依赖图能够被 elaboration；
- 所有传递 import 均能找到；
- 文件整体能单独编译。

它说明项目公共入口在编译层面可用。

### 5.2 API 回归测试

以下属于 API 回归：

- 用完整 theorem 名或点记法调用公开定理；
- 检查局部 `letI` 接口；
- 检查 relabelling、sewing、classification 和 conversion law；
- 检查公共名称与参数约定。

### 5.3 数学回归测试

以下更接近具体数学回归：

- product algebra 的 handle element；
- base-ring correlator；
- stable graph 的 genus；
- beta splitting；
- point-target intersection numbers；
- odd double factorial；
- Novikov 单项式乘法；
- formal derivative 的交换和乘积法则。

即使这些测试全部通过，也不能自动证明所有定义的 theorem statement 都准确表达了原始数学意图。

## 6. import 失败时如何定位

因为 `Basic.lean` 只有一个顶层 import，如果失败，应逐层缩小。

第一步：单独编译顶层入口：

```bash
lake env lean AxiomaticGW.lean
```

第二步：查看第一条失败诊断，并在 `AxiomaticGW.lean` 中找到对应直接 public import。

第三步：单独编译疑似模块。例如 Linear 路径：

```bash
lake env lean AxiomaticGW/Linear/Contraction.lean
```

第四步：继续沿 import 向下：

```bash
lake env lean AxiomaticGW/Linear/Copairing.lean
lake env lean AxiomaticGW/Linear/PerfectPairing.lean
```

第五步：搜索失败声明：

```bash
rg -n "失败声明名称" AxiomaticGW AxiomaticGWTest
```

第六步：区分三种失败：

- 传递 import 中的源模块错误；
- `Basic.lean` 某个具体 example 的 API 错误；
- 整个测试库或其他并行模块的独立错误。

不能仅因为 `lake build` 或 `lake test` 最终失败，就断言 `Basic.lean` 中某个 example 有错。

## 7. 如何分别编译

单独编译 `Basic.lean`：

```bash
lake env lean AxiomaticGWTest/Basic.lean
```

单独编译专门测试：

```bash
lake env lean AxiomaticGWTest/Linear/PerfectPairing.lean
```

编译专门 Lake target：

```bash
lake build AxiomaticGWTest.Linear.PerfectPairing
```

构建整个测试库：

```bash
lake build AxiomaticGWTest
```

运行项目配置的测试 driver：

```bash
lake test
```

构建默认生产库：

```bash
lake build
```

单文件编译最适合快速定位局部问题；测试库和全项目构建用于发现跨模块兼容性问题。两者不能互相取代。

## 8. `Basic.lean` 能否辅助验证 Linear

可以，但主要是集成层面的辅助。

它通过：

```text
AxiomaticGW
  -> Linear.Contraction
      -> Linear.Copairing
          -> Linear.PerfectPairing
```

间接编译整个 Linear 链。`namespace Contraction` 中的两个 examples 还直接验证 contraction 的重标号 API。大量 TFT、CohFT、GW examples 也间接依赖 pairing、copairing 和 contraction。

但它没有专门验证：

- `PerfectPairing.lean` 能否单独导入；
- 三个字段的准确公共类型；
- `toDual` 的最小假设；
- `toDual x y` 的第一槽约定；
- 点记法和完整限定名；
- 零模边界。

这些由 `Linear/PerfectPairing.lean` 补足。

## 9. `Basic.lean` 能否辅助验证 Frobenius

可以，而且比对 `PerfectPairing` 的覆盖更直接。

它验证了：

- local coalgebra instance；
- cocommutativity；
- base ring 和 product algebra；
- handle element；
- correlator 计算；
- separating/nonseparating sewing；
- Frobenius 到 TFT/CohFT 的转换；
- genus-zero 结合律；
- Frobenius classification round trip。

但它仍不能替代对 `Frobenius/Basic.lean`、`Constructions.lean`、`Coalgebra.lean`、`Examples.lean` 的逐文件数学审查。尤其是：如果某个 theorem statement 从一开始就表达了错误但可证明的命题，所有调用该 theorem 的 examples 仍可能编译通过。

## 10. `Basic.lean` 与专门测试文件的分工

`Basic.lean` 适合：

- 顶层 `import AxiomaticGW` smoke test；
- 跨层集成回归；
- 代表性的公共 API 使用；
- constant model 和具体数学计算；
- 检查上层接口能否组合。

专门测试文件适合：

- 只导入目标模块；
- 锁定最小类型类假设；
- 锁定字段、namespace、点记法和完整限定名；
- 锁定参数与槽位顺序；
- 添加目标模块特有的边界实例；
- 在源模块改变时给出快速、局部、容易诊断的错误。

因此，不建议把以后所有 `Copairing`、`Contraction` 和 Frobenius 的细粒度测试都继续堆入 `Basic.lean`。更合适的组织是：

```text
AxiomaticGWTest/Linear/PerfectPairing.lean
AxiomaticGWTest/Linear/Copairing.lean
AxiomaticGWTest/Linear/Contraction.lean
AxiomaticGWTest/Frobenius/Basic.lean
...
```

`Basic.lean` 保留为跨层公共 API 回归和顶层 smoke test，专门文件负责精确的模块级验证。

## 11. 实际编译结果和 warning

本次实际运行：

```bash
lake env lean AxiomaticGWTest/Basic.lean
```

结果 exit 0。直接单文件编译没有 warning。

运行：

```bash
lake build AxiomaticGWTest
```

测试库构建成功。Lake 的 module linter 对 `Basic.lean` 报告：

```text
The current module only contains private declarations.
```

运行：

```bash
lake test
```

结果 exit 0，同样只出现 `Basic.lean` 的 `privateModule` warning。

该 warning 的含义是 `Basic.lean` 只有私有测试声明，没有公共库声明；它不是数学、proof 或 elaboration 错误。本次任务明确禁止修改 `Basic.lean`，因此没有处理该既有 warning。

## 12. 为什么 `Basic.lean` 编译通过仍不代表数学全部正确

编译通过能证明：

- import 成功；
- 声明名称存在；
- 参数和类型类能够 elaboration；
- example proof term 符合声明的类型；
- 被调用 API 在当前项目版本中兼容。

编译通过不能自动证明：

- 源 theorem statement 就是作者真正想表达的数学结论；
- 假设没有使结论真空；
- 定义没有遗漏兼容性条件；
- 槽位、符号、方向和归一化符合原始数学来源；
- imports 没有通过偶然的 simp theorem 掩盖证明问题；
- 没有未被 `Basic.lean` 使用的错误声明；
- 整个 Linear 或 Frobenius 目录已经被全面审查。

因此正确流程始终是：先阅读和翻译定义、检查 theorem statement，再检查 proof、写抽象和具体回归测试，最后才用单文件编译、`lake test` 和 `lake build` 验证集成。
