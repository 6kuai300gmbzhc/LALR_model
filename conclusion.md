# LALR_Model 总结

## 项目目标

`LALR_Model` 建立了一个可执行的 LALR 分析器模型，并以 Isabelle/HOL 对其关键数据结构和执行语义进行形式化。项目同时提供 Python 工具：从 PLY 生成的 `parser.out` 报告读取 LALR 表，并依据该表识别记号流。两部分共享移进、归约、GOTO 与接受的基本运行模型。

## Isabelle/HOL 形式化结构

构建入口 `ROOT` 按以下依赖链加载理论：

1. `CFG.thy`：定义终结符/非终结符、产生式、上下文无关文法、单步推导、传递闭包推导和语言。语言由起始符号可推导出的纯终结符串构成。
2. `LALR_Table.thy`：将符号、记号和非终结符建模为字符串，状态和产生式编号建模为自然数；定义产生式记录、`Shift`/`Reduce`/`Accept` 动作及 LALR 表。`wf_table` 要求初始状态与移进/GOTO 目标合法、归约引用已存在产生式，并限制 `Accept` 只能发生在结束记号 `END` 上。
3. `LALR_Recognizer.thy`：定义分析配置（状态栈、带结束记号的输入、当前位置和执行轨迹）、逐步语义及错误类型。一次动作可移进、按产生式右部长度弹栈后 GOTO 并归约，或接受；不存在动作、产生式、GOTO 或栈不合法时产生可区分的拒绝结果。
4. `LALR_Properties.thy`：证明初始配置的栈、输入位置和结束记号性质，并给出 `pop_rhs` 的失败条件与成功时的长度性质。
5. `LALR_CFG_Bridge.thy`：把 LALR 表中的产生式映射到 CFG 产生式，定义表对 CFG 的表示关系、普通输入、表兼容性和更完整的 `lalr_table_certificate`。证书还检查终结符/非终结符不相交、结束记号存在、动作/GOTO 条目以及产生式符号的合法性。
6. `LALR_Invariant.thy`：定义已消费和剩余输入，并证明初始化时的输入不变式；单步运行保持原输入且位置只会不变或增加一。
7. `LALR_Items.thy`：定义 LR 项目、项目集、点后符号、项目推进和 GOTO；定义了闭包的一步扩展、有限迭代闭包和 canonical GOTO，并证明原项目集包含于有限闭包、良构性在有限闭包下保持，以及 canonical GOTO 的基本成员性质。新增外部 `state \<Rightarrow> item_set` 映射 `state_items` 和 `state_items_certificate`，用证书约束初始状态、Shift、非终结符 GOTO、Reduce 完成项目及项目集良构性；进一步证明 Shift/GOTO 的推进项目迁移和 Reduce action 的完成项目对应。当前还定义了状态项目的 token lookahead 映射、带 lookahead 的项目集、`lalr_lookahead_certificate`，以及分别约束 Shift、Reduce、Accept 动作的 `lalr_*_action_correct`；`lalr_table_generation_certificate` 将这些条件组合为表生成正确性接口，并由 `lalr_table_generation_certificateD` 分解。具体 FIRST/FOLLOW 传播算法和具体表的证书实例仍待补充。
8. `LALR_Stack.thy`：定义通用的良构状态栈和可达栈关系，证明良构栈非空、可达配置的状态栈保持良构，以及可达栈关系推出栈良构。
9. `LALR_Item_Stack.thy`：在栈项目一致性接口之外，定义实际可达 Reduce 迁移 `reduce_transition` 和抽象正确性条件 `reduce_transition_correct`。该条件要求每个实际 `s --Reduce--> g` 都落在由表状态、Reduce 产生式和 GOTO 目标构成的合法 Reduce graph 边中。
10. `LALR_Test.thy`：以算术表达式文法为例，手工给出 0--9 状态的 LALR 表，证明表良构，并通过 `eval` 验证 `A + A` 被接受、单独的 `PLUS` 被拒绝。归约秩不再手工给出：`LALR_Test.thy` 给出显式边表 `test_reduce_edges`，秩由 `auto_reduce_rank test_reduce_edges` 求值生成，`reduce_rank_check test_reduce_edges (auto_reduce_rank test_reduce_edges)` 由 `eval` 判定，覆盖引理 `test_reduce_graph_subset` 给出 `reduce_graph test_table ⊆ set test_reduce_edges`；逐边下降（`test_state_rank_certificate`）与无环性（`test_reduce_graph_acyclic`，经 `acyclicI_order`）都由该生成秩得到。终止性只需四条表事实 `wf_table_test_table`、`test_end_shift_free`、`test_reduce_graph_subset`、`test_reduce_rank_check`，经 schema 的 `termination_certificate_auto` 一行得到 `test_termination_certificate`，再以定理 `test_lalr_termination` 给出对任意输入 `toks` 的终止性（不再有 `assume`）。
11. `LALR_Rank_Auto.thy`：归约秩的可执行自动构造。`reduce_succs es s` 取边表中的后继集合，`reduce_rank_step es f s = Suc (Max (insert 0 (f ` reduce_succs es s)))` 走一轮高度迭代，`reduce_rank_iter` 对轮数做原语递归（零轮为常零），`auto_reduce_rank es = reduce_rank_iter es (Suc (length es))` 生成秩（燃料为边数加一）。`reduce_rank_check es r` 是对边表逐边要求 `r g < r s` 的可执行布尔检查器。`reduce_state_rank_certificate_auto`、`reduce_graph_acyclic_auto`、`reduce_rank_certificate_auto` 与 `finite_execution_certificate_of_reduce_graph_auto` 的前提只有 `reduce_graph t ⊆ set es` 和 `reduce_rank_check es (auto_reduce_rank es)`：既不需要状态集有限，也不需要预先给出秩函数。`auto_reduce_rank_chain`、`auto_reduce_rank_cycle` 用 `eval` 自检生成器在链上给出高度、在环上给出通不过检查的值。

12. `lalr_if_test.thy`：if 嵌套（dangling else）文法的 LALR 表，10 个状态、5 条产生式。其状态层 reduce graph 含有环 `7 → 9 → 7`：`if_reduce_graph_subset` 证出 `reduce_graph if_table ⊆ if_reduce_edges = {(2,1),(7,9),(8,9),(9,2),(9,7)}`，`if_generated_rank_check_fails` 用 `eval` 说明自动秩在该边表上通不过检查，`if_no_state_reduce_rank` 进一步证明不存在任何 `state ⇒ nat` 满足 `reduce_state_rank_certificate`。因此该表的终止性改用配置度量 `height_rank 2 if_height`（见下文），并由 `if_lalr_termination`、`if_lalr_terminates` 给出对任意输入 `toks` 的有限执行。

13. `LALR_Termination_Schema.thy`：统一的终止性证明格式。把 `finite_execution_certificate` 的六项义务中五项通用义务一次性消解（`finite_execution_certificateI`），并把唯一的表相关义务（Reduce 步严格下降）抽象为两个 provider：可执行自动秩（`termination_certificate_auto`，需要 `wf_table`、`end_shift_free`、边表覆盖与 `eval` 检查）与栈高/状态混合度量（`termination_certificate_height`，需要 `end_shift_free`、`height_reduce_ok` 与 `h` 的上界）；ε 归约被 `height_reduce_ok` 明确排除，并由 `height_reduce_ok_nonempty` 形式化记录。通用引理 `reduce_transition_correctI`、`reduce_step_stack_decomposition`、`pop_rhs_length_add`、`reduce_step_position`、`input_invariant_stepI` 也从各测试文件上移到这里；`termination_certificate_cases` 给出“一张表 + 任一 rank 证书 ⇒ 终止”的统一入口。

14. `complex_lalr_test.thy`：从 `scade_lalr` 的表达式 SCC 中抽出的最小规约环模型（状态 214/344 与共享 goto 上下文 233，规则 244 `Expr → Tempo_expr`、264 `Tempo_expr → PRE Expr`）。`reduce_graph` 恰为 `{(214,344),(344,214)}`：`complex_reduce_cycle_edges` 给出两条互反边，`complex_no_state_reduce_rank` 证明不存在状态秩；`complex_generated_rank_check_fails`（`eval`）说明自动秩对该边表也通不过检查（两个状态都收敛到 3）。终止性走 schema 的路线 B：`complex_height`（214 取 1，其余 0）、`complex_end_shift_free`、`complex_height_reduce_ok`、`complex_height_bound`，既得到 `complex_termination_certificate`，也用统一入口 `termination_certificate_cases` 得到 `complex_termination_certificate_cases`，最后是 `complex_lalr_termination`/`complex_lalr_terminates`。

识别器同时提供归纳关系 `run_rel` 和带 fuel 的递归执行器 `run_detailed_fuel`；定理 `run_detailed_fuel_iff_run_rel` 证明二者在相同步数下等价。面向调用者的 `recognize_detailed` 返回完整轨迹或具体错误，`recognize` 将结果简化为 `bool option`：`None` 表示燃料耗尽，`Some True/False` 分别表示接受/拒绝。

## Python 实现与测试

`lalr_recognizer.py` 解析 PLY 的规则、终结符、非终结符、状态、移进、归约和完成的增广起始项，构造 `LALRTable`。随后按状态栈执行 LALR 识别，记录每一步的状态、向前看记号和动作；命令行接口接受报告路径和记号序列，并以退出码区分接受和拒绝。

`test_lalr_recognizer.py` 使用随附的 `test_lalr` 报告验证：

- PLY 表元数据、产生式、ACTION 和 GOTO 的解析结果；
- 原子、加法和括号表达式等合法记号流会被接受；
- 非法前缀、缺失右操作数、缺失右括号和多余右括号会被拒绝；
- 成功轨迹至少包含移进、归约和最终接受动作。

## 当前保证与边界

项目已经形式化了表驱动 LALR 识别的局部运行规则，并证明了递归执行器与关系语义一致；它也定义了将表连接到 CFG 的兼容性/证书条件。当前理论尚未证明“满足证书的表对 CFG 语言完全正确”，即尚未给出识别器接受当且仅当输入属于 CFG 语言的完整健全性和完备性定理。Python 解析器经过示例报告测试，但没有自动导出 Isabelle 表，也没有建立 Python 实现与 Isabelle 形式化之间的机器可检验证明。

lookahead 与表生成证书目前刻画了正确性所需的接口：Reduce 只能在完成项目的 lookahead 中出现，Accept 必须对应带 `END` lookahead 的增广完成项目，Shift 则必须对应点后终结符并迁移到推进项目。它们尚未声称任意表自动满足这些条件，也尚未把 LALR lookahead 传播与 CFG 的 FIRST/FOLLOW 语义连接起来。

## 终止性框架

新增 `LALR_Termination.thy`，定义了 Shift 步、Reduce 步、阶段度量和基于 `measures` 的字典序关系。终止性条件统一封装为单一谓词 `termination_certificate t toks`，因此 `recognizer_termination` locale 的外部参数只有一个 LALR 表 `t`、一个输入串 `toks` 和一张证书。证书内部包含输入/表的结构条件、阶段秩接口以及任意配置有限执行的闭合条件；有限执行定理和带 fuel 识别器终止定理均从这张证书推出。阶段秩如何由 LR 项目集和可行前缀理论构造，仍是后续形式化工作。

针对 `LALR_Test.thy` 的算术表达式表，归约秩由 `auto_reduce_rank test_reduce_edges` 求值生成，并已证明 `reduce_state_rank_certificate test_table (auto_reduce_rank test_reduce_edges)`。生成值取自边表：0、1、4、6、7 ↦ 1，2 ↦ 2，3、8 ↦ 3，5、9 ↦ 4。`test_reduce_rank_check` 用 `eval` 判定逐边下降，`test_reduce_graph_acyclic` 经 `acyclicI_order` 得到无环性，`test_reduce_rank` 只是 `auto_reduce_rank test_reduce_edges` 的缩写，不再是独立的手工见证。配合可达栈状态不变式与桥接引理，已得到对任意有限输入 `toks` 的识别器终止性（见下节）。

`finite_execution_target` 单独表示有限执行结论。`termination_certificate` 现在显式定义为：存在一个可达性谓词和一个配置 rank，使 `finite_execution_certificate` 成立；因此不再把不足以推出终止的 `input_invariant_preserved`/`term_cond` 组合误当作完整证书。`termination_certificateD` 提取该有限执行证书，`termination_certificate_finite_execution` 和 `recognizer_termination.finite_execution` 将其转换为 `finite_execution_target`。

`LALR_Termination.thy` 现在定义了一般的 `reduce_graph`：其边由表中的 Reduce action、产生式和非终结符 GOTO 共同生成，并显式限制源/目标状态属于表状态集合。`finite_reduce_graph` 与 `finite_reduce_graphI/D` 给出有限状态表下的图有限性接口；`reduce_state_rank_certificate` 要求状态 rank 沿每条 Reduce 图边严格下降，`reduce_rank_of_state` 将状态 rank 提升为配置 rank，并由 `reduce_rank_of_state_decreases` 给出配置层下降定理。实际可达 Reduce 步落入该图仍需通过栈暴露状态和表证书证明。
在此基础上，`reachable_reduce_rank_decreases` 已证明：只要可达 Reduce 步满足 `reduce_graph_edge_certificate`，且状态 rank 满足 `reduce_state_rank_certificate`，则配置 rank 严格下降；`reduce_graph_rank_certificate` 将该结果直接转换为通用的 `reduce_rank_certificate`。
新增的 `finite_execution_certificate_of_reduce_graph` 进一步把该通用 rank 接入 `finite_execution_certificate`：调用者只需提供初始可达性、可达性保持、输入不变式、Shift 边界以及 Reduce 图边/rank 证书，即可得到以 `reduce_rank_of_state state_rank` 为 rank 的完整有限执行证书。

测试实例化的依赖链为：`test_table`、边表 `test_reduce_edges`、求值生成的秩 `auto_reduce_rank test_reduce_edges`（其覆盖性由 `test_reduce_graph_subset` 给出、逐边下降由 `eval` 判定的 `test_reduce_rank_check` 给出）、`wf_table test_table` 与可达栈状态不变式、`reduce_transition_correct test_table`、通用桥接引理，最终得到 `termination_certificate test_table toks` 和定理 `test_lalr_termination`（即 `finite_execution_target test_table toks`）与 `test_lalr_terminates`（`run_rel` 层的有限执行）。旧的测试专用终止 locale 及其三个 `assume` 已删除。

当前 Reduce 图依赖已抽象为 `reduce_transition_correct t`。`LALR_Termination.thy` 通过 `reduce_graph_edge_certificate_of_transition_correct` 将实际可达 Reduce 迁移连接到合法 Reduce graph，并在有限执行构造器中使用该接口和可达配置来源条件。该桥接引理已由辅助引理 `reduce_step_obtain` 与 `one_step` 定义展开证明，不再是 `sorry`。

### Reduce 秩的自动构造

`reduce_state_rank_certificate t state_rank` 只依赖有限图 `reduce_graph t`，所以秩问题是一个纯图论问题：存在自然数秩当且仅当该图无环；无环时的典范取法是图的高度，即从 `s` 出发的最长归约链长度加一，满足

  `auto_reduce_rank es s = 1 + Max {auto_reduce_rank es g | (s, g) ∈ set es}`（`es` 取 `reduce_graph t` 的边表）。

**旧做法的困难。** `LALR_Rank_Auto.thy` 的早期版本正是这样用 `wfrec` 把秩定义成图高度，并通过 `finite_acyclic_wf_converse` 得到良基性。该定义能通过证明检查，但不可执行：`reduce_graph` 的定义是 `state`（即 `nat`）上的集合概括，代码生成时要求元素类型带有 `enum` 实例，于是代码生成器报

  Wellsortedness error: Type nat × nat not of sort enum

后果是任何具体秩值都无法靠求值得到，只能手工展开表结构逐条重算 ACTION 的 `map_of` 查找——这正是原先“自动赋值无法导出、耗时过长”的来源。仅把 `wfrec` 换成别的递归算子并不能解决，问题出在集合概括本身。

**现在的做法。** 把边表 `es` 作为显式参数，高度迭代只用到 `filter`、`map`、`Max` 与加法：

- `reduce_succs es s = set (map snd (filter (λe. fst e = s) es))`；
- `reduce_rank_step es f s = Suc (Max (insert 0 (f ` reduce_succs es s)))`；
- `reduce_rank_iter es 0 = (λ_. 0)`，`reduce_rank_iter es (Suc n) = reduce_rank_step es (reduce_rank_iter es n)`；
- `auto_reduce_rank es = reduce_rank_iter es (Suc (length es))`。

这些常数都有代码方程，故 `auto_reduce_rank` 可直接求值、也可 `export_code`。燃料取边数加一的依据是：无环链上的边两两不同，最长链长度不超过 `length es`，高度不超过燃料轮数；对含环的边表，生成器同样给出一个值，只是无法通过下面的检查。

**证书。** `reduce_rank_check es r` 是边表上的可执行布尔函数，逐边要求 `r g < r s`。于是每个具体表只需两步：证明一次覆盖 `reduce_graph t ⊆ set es`（超集即可，多余边只会让条件更强而不会破坏正确性），再用一次 `by eval` 判定 `reduce_rank_check es (auto_reduce_rank es)`。定理 `reduce_state_rank_certificate_auto`、`reduce_graph_acyclic_auto`、`reduce_rank_certificate_auto` 与 `finite_execution_certificate_of_reduce_graph_auto` 就把这两条前提变成原有的终止性接口，不再需要 `finite (states t)`，也不再需要调用者提供任何秩函数。`auto_reduce_rank_chain` 与 `auto_reduce_rank_cycle` 用 `eval` 自检：前者在有向链上给出高度 3，后者在环上给出通不过检查的值。

**测试表。** `test_reduce_edges` 恰为 9 条边：`2 → 1`，`3 → {2,7}`，`5 → {3,8}`，`8 → {2,7}`，`9 → {3,8}`。`test_reduce_graph_subset` 先用 `test_reduce_actions` 把归约状态分成 5 类，再用“GOTO 目标只由非终结符决定”的三条引理（`test_goto_Eprime`、`test_goto_E`、`test_goto_T`，无需状态前提）定出目标，逐类完成覆盖证明；这样避免了旧版在 22 条 ACTION 的 `if` 链上 `auto` 发散的问题。`test_reduce_rank_check` 由 `eval` 判定，生成取值为 0、1、4、6、7 ↦ 1，2 ↦ 2，3、8 ↦ 3，5、9 ↦ 4（`test_reduce_rank_values` 逐点由 `eval` 验证）。

旧版 `LALR_Rank_Iter.thy`（以表为参数、以“迭代在 `card (states t)` 轮后稳定”为前提的版本）依赖被删除的 `auto_reduce_rank t`，已移到 `attic/` 不再构建。它的数学内容（无环性蕴含迭代稳定，从而给出不动点证书）仍然成立，可以另行补回；当前实现选择“生成 + 可执行检查”，因为该检查是 ground 计算，不需要为每张表做归纳。

需要注意两点：(1) `reduce_graph` 是表级过近似，它只要求存在 GOTO 前驱 `s'`，因此可能含有真实运行中不会出现的边；这些多余边只会让无环性更难满足，可用项目集证书收紧。(2) `reduce_rank_of_state` 只取栈顶状态，因此要求每条 Reduce 边在栈顶层严格下降；当 |rhs| ≥ 2 时栈高本身已下降，此时也可改用栈高的字典序度量。

### 反例：if 嵌套文法与状态秩的不存在

`lalr_if_test.thy` 给出一个取自 dangling-else 的 LALR 表：产生式 `S → Start`、`Start → IfBlock`、`IfBlock → IF ID THEN ElseClause`、`ElseClause → ELSE IfBlock`、`ElseClause → ELSE ID`，10 个状态。它的归约动作把状态 7 归约到 9、又把状态 9 归约到 7（`if_reduce_cycle_edges`），所以 `reduce_graph if_table` 含有环 `7 → 9 → 7`。

由此得到三条结论，全部在文件中是定理：

- `if_reduce_graph_subset`：`reduce_graph if_table ⊆ {(2,1),(7,9),(8,9),(9,2),(9,7)}`（边表 `if_reduce_edge_list` 即此顺序，`if_edges_set_eq` 给出集合相等）；
- `if_generated_rank_check_fails`：`¬ reduce_rank_check if_reduce_edge_list (auto_reduce_rank if_reduce_edge_list)`，由 `eval` 判定——生成器对环上的状态只能给出同一个值（此处 2 取 2，7、8、9 都取 6），故边 `7 → 9` 与 `9 → 7` 无法同时满足严格下降；
- `if_no_state_reduce_rank`：`¬ (∃rank. reduce_state_rank_certificate if_table rank)`。

最后一条说明这不是生成器的缺陷：状态层秩存在的充要条件是 `reduce_graph` 无环，而该表有环，所以任何 `state ⇒ nat` 都不可能是归约秩。`auto_reduce_rank` 的“失效”是数学事实，而非实现缺陷。

终止性仍然成立，因为框架只要求存在一个在每条可达归约步上严格下降的配置度量。文件现在把它写成 schema 的路线 B：`if_height s = (if s = 2 then 1 else 0)`，度量是

  `height_rank 2 if_height cfg = 2 * length (state_stack cfg) + (if top_state (state_stack cfg) = Some 2 then 1 else 0)`

即栈高的两倍再加一个“栈顶是状态 2”的指示位。关键观察是：四条归约规则里只有状态 2 上的 `Start ⇐ IfBlock`（`if_p1`，右部长度 1）保持栈高（弹 1 压 1），其余三条右部长度都大于 1，归约后栈高严格下降；而保持栈高的那一步把栈顶从 2 换成 GOTO 目标 1，指示位由 1 变 0。于是 `if_height_reduce_ok : height_reduce_ok if_table if_height` 成立，上界由 `if_height_bound : if_height s < 2` 给出。环 `7 → 9 → 7` 上的两步分别弹掉 2 个和 4 个状态，栈高每步都在降，这正是该度量能处理环的原因。

其余部分全部由 schema 提供：`reduce_step_stack_decomposition` 把一次归约分解为“弹栈、取 GOTO 目标”，`input_invariant_stepI` 证明输入不变式在位置到达 `length toks` 之后仍然保持（此时 lookahead 必为 `END`，而 `if_end_shift_free` 排除 shift），`finite_execution_certificate_height` 组出证书，最后由 `if_termination_certificate`、`if_lalr_termination`（`finite_execution_target if_table toks`）与 `if_lalr_terminates`（存在有限执行 `run_rel`）各一行收尾。

教训：自动秩只能做到“图无环时给出高度”；一旦归约图有环，就必须把栈或输入纳入度量。框架本身不限制度量的形状（`finite_execution_certificate` 的 rank 是 `config ⇒ nat`），所以这类表仍可完全自动地完成终止性证明——只是不能只靠 `auto_reduce_rank`。

### 反例：表达式强连通分量的最小规约环

`complex_lalr_test.thy` 从 SCADE 表达式 SCC 中保留一对互反规约边及其共享 goto 上下文 233：

- state 214 按 Rule 244 `Expr → Tempo_expr` 规约，经 `goto(233, Expr)` 到 state 344；
- state 344 按 Rule 264 `Tempo_expr → PRE Expr` 规约，经 `goto(233, Tempo_expr)` 回到 state 214。

因此 `reduce_graph` 恰含状态环 `214 → 344 → 214`，`complex_no_state_reduce_rank` 证明任何仅依赖当前状态的自然数秩都不可能沿所有边严格下降。该文件是聚焦于 reduce graph 的小型抽象子表，不是完整可识别的 SCADE 子 parser。规约 244 的 RHS 长度为 1，配置秩为它设置状态权重 `h(214)=1`、`h(344)=0`；规约 264 的 RHS 长度为 2，会使状态栈变短。由 `height_reduce_ok` 和 schema 的栈高/状态混合度量，模型仍有 `complex_lalr_termination`；`complex_termination_certificate_cases` 则演示用统一入口（`termination_certificate_cases`）而不是直接调用 provider 来完成同一件事。自动秩在该表上的行为一并记录：`complex_generated_rank_check_fails` 用 `eval` 判定它通不过检查，`complex_generated_rank_values` 给出两个状态都收敛到 3（fuel = 3），与 if 表的情形一致。

## 统一的终止性证明格式

`LALR_Termination_Schema.thy` 把两条路线（可执行自动秩、栈高/状态混合度量）整合为同一套接口。核心是 `finite_execution_certificate` 的六项义务：其中五项（初始可达、可达保持、输入不变式初始与保持、Shift 边界）与具体表无关，由 `finite_execution_certificateI` 一次消解；唯一与表相关的只剩“Reduce 步的严格下降”。格式因此是：

- 通用前提（所有表）：`end_shift_free t`（`END` 上不允许 shift），以及由 `reduce_transition_correctI` 从 `wf_table t` 得到的 `reduce_transition_correct t`；
- rank 义务二选一：
  - 路线 A（图无环）：给出边表 `es`，证明 `reduce_graph t ⊆ set es` 与 `reduce_rank_check es (auto_reduce_rank es)`（后者是 ground 计算，`by eval` 即可），由 `termination_certificate_auto` 收尾；
  - 路线 B（图可能有环）：给出 `h :: state ⇒ nat` 与上界 `B`，证明 `height_reduce_ok t h` 与 `⋀s. h s < B`，由 `termination_certificate_height` 收尾。

两条路线都直接给出 `termination_certificate t toks`，再由 `termination_certificate_finite_execution` 得到 `finite_execution_target t toks` 与有限执行 `run_rel`。统一入口是

  `termination_certificate_cases: wf_table t ⟹ end_shift_free t ⟹ ((reduce_graph t ⊆ set es ∧ reduce_rank_check es (auto_reduce_rank es)) ∨ (height_reduce_ok t h ∧ (∀s. h s < B))) ⟹ termination_certificate t toks`

于是每张表的义务固定为四条（路线 A：`wf_table`、`end_shift_free`、边覆盖、`eval` 检查）或三条（路线 B：`end_shift_free`、`height_reduce_ok`、高度上界），全部是文件内可机械检查的引理。`LALR_Test.thy` 用 `wf_table_test_table`、`test_end_shift_free`、`test_reduce_graph_subset`、`test_reduce_rank_check` 四条即得 `test_termination_certificate`；`lalr_if_test.thy` 用 `if_end_shift_free`、`if_height_reduce_ok`、`if_height_bound` 三条即得 `if_termination_certificate`；`complex_lalr_test.thy` 更进一步直接用统一入口：`termination_certificate_cases [OF complex_wf_table complex_end_shift_free]` 之后只需给出路线 B 那一个析取支。

通用辅助引理也一并上移，避免每张表重复：`reduce_step_stack_decomposition`（一次归约分解为弹栈 + GOTO）、`pop_rhs_length_add`、`reduce_step_position`（归约不改输入位置）、`input_invariant_stepI`（输入不变式保持，需要 `end_shift_free`）。`height_rank_less_shorter`、`height_rank_less_same_length` 与 `encoded_less_le` 是路线 B 的算术核心（`height_rank B h = B * |stack| + 栈顶权重` 的编码比较，只要求权重恒小于 `B`）。

### 消融实验（哪些部分是承重的）

用“删除—重建”的方式逐项检查，只有仍能通过 `isabelle build` 的删除才保留：

| 消融项 | 操作 | 结果 |
|---|---|---|
| 包装定理 | 删除 `finite_execution_target_auto/_auto_wf/_height`、`run_rel_auto/_auto_wf/_height` 六个定理 | 通过 ⇒ 它们只是 `termination_certificate_*` 与框架推论 `termination_certificate_finite_execution`、`finite_execution_certificateD` 的重述 |
| 重复入口 | 把“`reduce_transition_correct` 版”与“`wf_table` 版”的 `termination_certificate_auto` 合并为一个（`wf_table` 版，内部用 `reduce_transition_correctI`） | 通过 ⇒ 每表少一条义务，`correct` 不再出现在接口上 |
| 前提 `0 < B` | 从 `reduce_step_height_decrease`、两个 `*_height` 定理与 dispatcher 中删除 | 通过（首次失败仅因 `B` 无法从 premise 推断，在 dispatcher 中用 `where B = B` 固定后即通过）⇒ 该前提对证明冗余，已删除 |
| 引理 `reduce_rank_of_state_less` | 删除 | 通过 ⇒ 无人引用（调用方用 `bound[of g]` 就地得到同一事实） |
| `LALR_Test` 的死引理 | 删除 `test_shift_consumes_token`、`test_productions_0`、`test_reduce_rank_certificate`、`test_reduce_transition_correct` | 通过 ⇒ 前者是旧路线的残留，`test_reduce_rank_certificate` 与 `test_state_rank_certificate` 只差一次 `unfolding` |
| 前提 `height_reduce_ok` 与 `⋀s. h s < B` | 从 `reduce_step_height_decrease` 删除 | **失败**：`Undefined fact: "ok"`（分类讨论处）、`reduce_rank_of_state h cfg' < B` 无法证（界处）、证书最后的 `show` 报 `OF: no unifiers` ⇒ 两条前提都承重 |
| 前提 `end_shift_free` | 从 `finite_execution_certificate_height` 删除 | **失败**：`input_invariant_stepI` 需要它排除 `END` 上的 shift |
| ε 归约 | 保持 `height_reduce_ok` 中的 `2 ≤ |rhs| ∨ (|rhs| = 1 ∧ h g < h s)`，并新增 `height_reduce_ok_nonempty: … ⟹ 0 < length (rhs p)` | 保留限制：ε 归约既不降栈高也不换栈顶，`B * |stack| + h (top)` 无法在其上下降 ⇒ 若放开会直接破坏路线 B 的可靠性 |

注意 `height_reduce_ok` 排除了空右部（ε）归约：它既不降栈高也不换栈顶，任何只依赖栈形状的度量都无法在它上面下降。本项目的表都不含 ε 产生式；若将来需要支持，应在这两个分量之外引入输入位置或其他分量。

## 终止性证明的完成情况

原先 `LALR_Test.thy` 的 `test_lalr_termination` locale 依赖三个 `assume`（`generation`、`reduce_correct`、`certificate`）。现在处理如下：

1. `generation` 已从终止性路线中删除。它不参与 `recognizer_termination` 的推导（终止性只需有限执行证书），并且按原参数 `bound = 0`、`initial_items = {}` 是不可满足的：`state_items_certificate test_table m 0 {}` 先强制状态 0 的项目集为空，再经 `gotos test_table 0 ''T'' = Some 3` 强制状态 3 为空，而 Reduce 子句又要求完成项目 `(3,1)` 属于状态 3。它属于表生成/正确性路线，应以 `initial_items = {(0,0)}`、`bound ≥ 4` 以及具体的 `state_item_map`/`state_lookahead_map` 重新实例化，这仍是待补部分。
2. `reduce_correct` 这条义务已在 schema 内部消解：`termination_certificate_auto` 用 `reduce_transition_correctI` 从 `wf_table` 推出 `reduce_transition_correct`（依据是良构栈上的状态都属于 `states t`、`pop_rhs` 结果是栈前缀）。因此测试文件里不再需要 `test_reduce_transition_correct` 这样的中间引理。
3. `certificate` 已成为引理 `test_termination_certificate`（对任意 `toks` 的 `termination_certificate test_table toks`）：`termination_certificate_auto [OF wf_table_test_table test_end_shift_free test_reduce_graph_subset test_reduce_rank_check]` 一行，rank 为 `reduce_rank_of_state (auto_reduce_rank test_reduce_edges)`。六项证书义务、可达性取 `reachable_cfg test_table toks`、以及输入不变式保持（通用的 `input_invariant_stepI`：位置不会越过 `length toks`，因为 `END` 上没有 shift）全部由 schema 消解。

最终 `test_lalr_termination` 是定理（不再有 `assume`），并由 `recognizer_termination` locale 得到 `finite_execution_target test_table toks`。

工程上，`LALR_Item_Stack.thy` 的 `quick_and_dirty` 已收窄为仅包围仍未完成的 `reachable_stack_item_consistent`（`sorry`），其余理论（包括 `LALR_Termination.thy` 与 `LALR_Test.thy`）都在普通模式下接受检查。整个会话用 `isabelle build -D .` 构建通过（`LALR_Rank_Iter.thy` 已移入 `attic/`，不再参与构建；统一的终止性格式在 `LALR_Termination_Schema.thy`）。

`lalr_if_test.thy` 另外用配置度量（`height_rank 2 if_height`）完成了 if 嵌套表的终止性证明（`if_lalr_termination`、`if_lalr_terminates`），尽管该表不存在状态秩（`if_no_state_reduce_rank`）。可见“自动秩”与“终止性”是两件事：前者依赖归约图无环，后者只需要一个合适的测度；`lalr_if_test` 与 `LALR_Test` 分别覆盖了这两条路线（schema 的路线 B 与路线 A）。整会话（含 schema 与 `lalr_if_test`）由 `isabelle build -D .` 通过。

## 语言等价性：M1（可靠性）已完成

终止性路线收尾后，代码库另开一条“表与文法语言一致”的路线（方案见 `plan_equivalence.md`）。第一阶段 M1 只做**可靠性**（识别器只接受文法能生成的字），已全部通过 `isabelle build -D .`。

1. `LALR_Symbol_Stack.thy`（424 行）：符号栈与 yield 关系。
   - `stack_symbols t toks cfg σ`：从空栈出发，shift 追加 `Terminal (lookahead)`，reduce 把 `rhs` 换成 `[Nonterminal (lhs p)]`（`take (length σ - length (rhs p)) σ @ [Nonterminal (lhs p)]`）。
   - `parses G σ w`：`σ` 能产出 `w`（terminal / nonterminal / nil 三条规则），并给出 `parses_derives`（`parses ⇒ derives`）、`parses_append`、`parses_append_split` 等组合引理。
   - `tracks t items σ s` 与 `stack_tracks t items σ stk`：状态 `s` 的项目集里每个项目的点与 `σ` 的尾部一致（整栈版本要求 `length σ + 1 = length stk`，且每个位置 `j` 追踪 `take j σ`）。
2. `LALR_Soundness.thy`（916 行）：沿运行维护不变量
   `parser_invariant G t items toks cfg = input_invariant toks cfg ∧ (∃σ. stack_symbols … σ ∧ stack_tracks … σ (state_stack cfg) ∧ parses G σ (map Terminal (consumed_tokens cfg)))`，
   并对 shift（`state_items_certificate` 的 shift 子句 + `tracks_append_symbol`）与 reduce（`reduce_step_stack_decomposition` + 在栈顶状态上完成的项强制 `σ` 以 `rhs p` 结尾 + `parses_replace_suffix`）分别证明保持。
3. 主定理 `accepts_sound`：
   `lalr_sound_certificate G t items bound initial_items lookaheads ⟹ (∀item ∈ initial_items. snd item = 0) ⟹ accept_shape ⟹ ordinary_input t toks ⟹ accepts t toks ⟹ toks ∈ language G`。
   接受步把 lookahead 定为 `end_token`，由 `ordinary_input` 得输入已读完（`consumed_tokens cfg = toks`）；`lalr_accept_action_correct` 给出增广起始产生式的完成项，追踪把符号栈压成 `[Nonterminal (SS G)]`，于是 `parses_derives` 给出推导。
4. 两条**显式**义务（不来自项目证书，故保留为假设）：
   - `lalr_sound_certificate` 的最后一合取：每条 reduce 动作都对应真实文法产生式（用于 `parses_replace_suffix`）；
   - `accept_shape`：接受时 `length (state_stack cfg) = 2`（即方案中的 C6“起始状态无入边”）。
   两者都应在表生成端（M2 起的实例化）证明，而不是在可靠性定理里假设掉。
5. 工程：仓库在 `LALR_Model/` 内独立初始化（父目录 `.git` 不可写），提交 `7e3eb92`（基线）、`52f9dc4`（Symbol_Stack）、`054a050`（Soundness）。`ROOT` 已按依赖顺序插入 `LALR_Symbol_Stack`、`LALR_Soundness`。

**尚未做的**：完备性（`accepts_complete`，需 lookahead 语义、无冲突与动作全定义三条新证书，见 `plan_equivalence.md` 的 C2–C4）、以及把 `lalr_sound_certificate` 与 `accept_shape` 在 `LALR_Test`/`lalr_if_test`/`complex_lalr_test` 上实例化（M2）。
