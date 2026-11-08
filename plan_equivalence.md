# 从「终止性」到「语言一致性」：后续证明架构（方案）

本文给出 `LALR_Model` 从当前状态（识别器语义 + 终止性证书）走到最终目标
「某张 LALR 表接受的语言恰好是某个 CFG 的语言」所需的理论分层、证书补强、
定理形状、实例化路线与风险。**本文件只是方案，不含新代码。**

---

## 0. 目标定理

对一张表 `t`、文法 `G`，最终要的是：

```isabelle
theorem accepts_iff_language:
  "ordinary_input t toks ⟹ accepts t toks ⟷ toks ∈ language G"
```

再加一个可执行版本（`recognize` 是带 fuel 的确定性执行器）：

```isabelle
theorem recognize_iff_language:
  "ordinary_input t toks ⟹ (∃fuel. recognize fuel t toks = Some True) ⟷ toks ∈ language G"
```

`ordinary_input` 这个前提不能省：`accepts` 是「跑到 Accepted」的存在性命题，而
`toks` 里若混入 `END`，识别器可能在 `position < length toks` 时看到 `END` 而接受，
此时接受的串并不是 `toks`。所以契约应写成
`toks ∈ language G ⟷ (ordinary_input t toks ∧ accepts t toks)`，
或把 `ordinary_input` 作为前提。

分解成两个方向：

| 方向 | 断言 | 数学内容 | 需要的证书 |
|---|---|---|---|
| 可靠性 sound | `accepts t toks ⟹ toks ∈ language G` | 接受 ⟹ 栈上的符号确实拼出一个推导 | items 追踪（不需要 lookahead 语义） |
| 完备性 complete | `toks ∈ language G ⟹ accepts t toks` | 沿最右推导逆向模拟，永不报错 | lookahead 语义 + 动作确定性 + 动作全定义 |

关键观察：**两个方向需要的证书不一样**。可靠性只需要 `state_items_certificate`
（现有）+ `table_represents_cfg`（现有）；完备性才需要 lookahead 的语义正确性、
无冲突与全定义。因此建议先做可靠性（便宜、风险低），再做完备性。

---

## 1. 现状盘点

已有（`ROOT` 顺序）：

| 层 | 理论 | 已有内容 | 对等价性证明的作用 |
|---|---|---|---|
| 文法 | `CFG.thy` | `derives1`/`derives`/`language` | 目标语言的唯一定义 |
| 机器 | `LALR_Recognizer.thy` | `one_step`、`run_rel`、`reachable_cfg`、`recognize` | 被证明对象的语义 |
| 桥 | `LALR_CFG_Bridge.thy` | `table_represents_cfg`、`lalr_table_certificate`、`accepts` | 表 ↔ 文法的对应契约 |
| 项目 | `LALR_Items.thy` | item/closure/canonical goto、`state_items_certificate`、lookahead 证书、三个 action 正确性、`lalr_table_generation_certificate` | 完备性的主要素材 |
| 栈 | `LALR_Stack.thy` / `LALR_Item_Stack.thy` | `stack_well_formed`、`reachable_stack_well_formed`、`stack_item_consistent`、相邻 item 迁移 | 栈不变量的一半 |
| 终止 | `LALR_Termination.thy` + `..._Schema.thy` + `LALR_Rank_Auto.thy` | 统一终止格式、两条 rank 路线 | 让 `recognize` 不再返回 `None` |

结论：**局部机器语义、栈良构、item 迁移、终止性都有了；缺的是「栈符号 ↔ 推导」这一层，
以及「表在合法前缀上一定有唯一正确动作」这一层。**

`conclusion.md` 第 44 行自己也点明了：尚未证明「满足证书的表对 CFG 语言完全正确」。
另外 `conclusion.md` 第 168 行说 `LALR_Item_Stack.thy` 还有 `quick_and_dirty` + `sorry`，
但当前磁盘上的文件已经没有 sorry 了（`grep` 全库为零），该行需要更新。

---

## 2. 缺口：证书要补的六处

现有 `lalr_table_generation_certificate` 是「表按 LR 规范方式构造」的*必要*条件，
但不足以推出语言等价。按用途列出缺什么：

**(C1) `initial_items` 没有被约束。**
`state_items_certificate` 只说 `state_items items (start_state t) = item_closure t bound initial_items`，
而 `initial_items` 是自由参数（`conclusion.md` 第 162 行也记了这一点）。
应钉死为增广起始项：`initial_items = {(aug_id, 0)}`，其中 `aug_id`/`aug` 来自
`augmented_start_wf` 或 `lalr_accept_action_correct`。否则「初态的项目集全是点 0 项」这一步无法证，
而它是栈追踪的归纳基。

**(C2) lookahead 没有语义。**
`lalr_lookahead_certificate` 只说 `state_item_lookaheads ⊆ terminals t`。
完备性要求：`tok ∈ lookaheads s (rid, k)` ⟹ `tok` 确实能跟在 `lhs` 后面
（即 FOLLOW 意义上的「合法后继终结符」）。需要新增语义条件（可命名为
`lalr_lookahead_sound`），并在实例里由「算出 FOLLOW + 证明 FOLLOW 可靠 + `eval` 检查包含关系」来兑现。

**(C3) 没有无冲突（决定性）条件。**
同一 `(s, tok)` 上同时存在「可移进项」和「带该 lookahead 的完成项」时，LALR 表只能二选一；
完备性必须知道表选的就是规范构造该选的那个。需要一个 `lalr_action_determined`：
移进/归约/接受三种情形互斥，且同一 lookahead 下至多一个完成项。

**(C4) 没有动作全定义（totality）。**
合法前缀 + 合法 lookahead 出现时，`actions t s tok ≠ None` 必须成立，否则完备性会在
`step_no_action` 处失败。这就是「该文法是无冲突 LALR(1)」在表上的体现。

**(C5) 状态与项目集没有单射。**
要证「接受时栈恰好是 `[start, acc]`」，需要 `state_items` 单射
（不同状态项目集不同，规范 LALR 构造里状态就是项目集）。否则两个状态可以共享项目集，
接受状态的唯一性无从谈起。

**(C6) 起始状态没有「无入边」条件。**
同理，要证接受时栈高为 2，需要 `start_state` 不能被任何 shift/goto 指向
（规范表里状态 0 正是这样）。

补强后的总证书建议命名为 `lalr_parser_certificate G t items lookaheads bound initial_items`
（新理论里定义，避免改动既有接口），它 = 现有
`lalr_table_certificate` + `lalr_table_generation_certificate` + C1–C6。

顺带一个可组合性引理：`action_entries_wf t` 已经蕴含
`(tok = end_token ⟶ a ≠ ActShift q)`，所以

```isabelle
lemma end_shift_free_of_lalr_table_certificate:
  "lalr_table_certificate G t ⟹ end_shift_free t"
```

——终止性证书要求的外在义务，其实已经含在语言证书里；两张证书可以直接拼在一张表上。

---

## 3. 分层架构

依赖图（新理论用 `＋` 标注）：

```
CFG ─ LALR_Table ─ LALR_Recognizer ─ LALR_Properties
                         │
                    LALR_CFG_Bridge ── LALR_Invariant
                         │
                    LALR_Items ─── LALR_Stack ─── LALR_Item_Stack
                         │
      ＋CFG_FIRST_FOLLOW ─┤
                         ├─＋LALR_Symbol_Stack
                         │        │
                         │   ＋LALR_Soundness
                         │        │
                         │   ＋LALR_Completeness
                         │        │
                         └──＋LALR_Equivalence ──(实例)── LALR_Instance_*
```

### 3.1 `CFG_FIRST_FOLLOW.thy`（新增）

只服务完备性，可独立完成、独立验证。

```isabelle
inductive first :: "'a cfg ⇒ 'a grammar_symbol list ⇒ 'a set"   (* 或单调闭包定义 *)
inductive follow :: "'a cfg ⇒ 'a ⇒ 'a set"

lemma first_sound:
  "a ∈ first G α ⟹ ∃β. derives G α (Terminal a # β)"
lemma follow_sound:
  "a ∈ follow G A ⟹ ∃α β. derives G [Nonterminal (SS G)] (α @ [Nonterminal A, Terminal a] @ β)"
```

实现要点：用 `inductive_set`（最小闭包）比 `primrec` 好，因为 FIRST 对可空串要递归；
证明只用「最小闭包 + 规则反演」。这类证明在本仓库里已有成熟套路（`derives1`/`derives` 的归纳）。

### 3.2 `LALR_Symbol_Stack.thy`（新增，可靠性与完备性共用）

**(a) 符号栈关系。** `config` 里只有状态栈，符号栈必须由运行轨迹重建：

```isabelle
inductive stack_symbols ::
  "lalr_table ⇒ token list ⇒ config ⇒ symbol list ⇒ bool" where
  symbols_init: "stack_symbols t toks (init_config t toks) []"
| symbols_shift:
    "stack_symbols t toks cfg σ ⟹ one_step t cfg = Next cfg' ⟹
     top_state (state_stack cfg) = Some s ⟹
     actions t s (input_tokens cfg ! position cfg) = Some (ActShift st) ⟹
     stack_symbols t toks cfg' (σ @ [Terminal (input_tokens cfg ! position cfg)])"
| symbols_reduce:
    "stack_symbols t toks cfg σ ⟹ one_step t cfg = Next cfg' ⟹
     top_state (state_stack cfg) = Some s ⟹
     actions t s (input_tokens cfg ! position cfg) = Some (ActReduce rid) ⟹
     productions t rid = Some p ⟹
     stack_symbols t toks cfg' (take (length σ - length (rhs p)) σ @ [Nonterminal (lhs p)])"
```

注意归约规则用 `take` 截断，**不**假设被截掉的正好是 `rhs p`；后者是可靠性证明里的
`reduce_rhs_match` 引理要证的结论（来自 items 追踪）。这样关系对给定 `σ` 是确定的。

**(b) 产出（yield）关系。** 「栈上符号拼出的终结符串」：

```isabelle
inductive parses :: "symbol cfg ⇒ symbol list ⇒ symbol list ⇒ bool" where
  parses_nil: "parses G [] []"
| parses_terminal: "parses G σ w ⟹ parses G (Terminal a # σ) (Terminal a # w)"
| parses_nonterminal:
    "(A, α) ∈ set (RR G) ⟹ parses G α w1 ⟹ parses G σ w ⟹
     parses G (Nonterminal A # σ) (w1 @ w)"

lemma parses_derives: "parses G σ w ⟹ derives G σ w"
lemma parses_append_terminal: "parses G σ w ⟹ parses G (σ @ [Terminal a]) (w @ [Terminal a])"
lemma parses_append_split: "parses G (α @ β) w ⟹ ∃w1 w2. w = w1 @ w2 ∧ parses G α w1 ∧ parses G β w2"
```

`parses` 是「每个符号各自派生出一段终结符串、按顺序拼接」的归纳定义，等价于存在一片森林；
它避开了显式语法树，做归纳更省。

**(c) items 追踪。** 栈上每个位置的状态，其项目集必须与「该位置之前的符号」一致：

```isabelle
definition tracks :: "lalr_table ⇒ state_item_map ⇒ symbol list ⇒ state ⇒ bool" where
  "tracks t items σ s ⟷
     (∀item ∈ state_items items s.
        snd item ≤ length σ ∧
        take (snd item) (rhs (the (productions t (fst item)))) =
          drop (length σ - snd item) σ)"

definition stack_tracks ::
  "lalr_table ⇒ state_item_map ⇒ symbol list ⇒ state list ⇒ bool" where
  "stack_tracks t items σ stk ⟷
     length σ + 1 = length stk ∧
     (∀j < length stk. tracks t items (take j σ) (stk ! j))"
```

要点：**每个状态**都要追踪自己那段前缀，而不只是栈顶——归约后新的栈顶是弹栈后的状态 `s'`，
它的追踪事实必须来自它原先作为「更深处状态」时的不变量。

### 3.3 `LALR_Soundness.thy`（新增）

不变量打包成一个谓词（`σ` 存在量化）：

```isabelle
definition parser_invariant :: "symbol cfg ⇒ lalr_table ⇒ token list ⇒
   state_item_map ⇒ config ⇒ bool" where
  "parser_invariant G t toks items cfg ⟷
     (∃σ. stack_symbols t toks cfg σ ∧
          parses G σ (map Terminal (consumed_tokens cfg)) ∧
          stack_tracks t items σ (state_stack cfg) ∧
          length σ = length (state_stack cfg) - 1)"
```

主引理（对 `reachable_cfg` 归纳）：

| 引理 | 内容 | 依赖 |
|---|---|---|
| `stack_symbols_pop` | 符号栈截断与 `pop_rhs` 一致 | 定义 |
| `stack_tracks_shift` | 移进后新状态的追踪成立 | `state_items_certificate` 的 shift 子句 + `goto`/`closure` 成员引理（**需补：closure 新增项皆为点 0**） |
| `stack_tracks_reduce` | 弹栈后新栈顶（经 goto）的追踪成立 | goto 子句 + 前缀传递 |
| `reduce_rhs_match` | 完成项 `(rid, |rhs p|)` 在栈顶 ⟹ 符号栈以 `rhs p` 结尾 | 追踪 + `take`/`drop` 列表引理 |
| `invariant_preserved` | `reachable_cfg ⟹ parser_invariant` | 以上诸条 |
| `accept_stack_shape` | 接受配置的状态栈恰为 `[start_state, acc]`，符号栈恰为 `[Nonterminal (SS G)]` | C5、C6 + 接受状态是 `goto(start, S)` 的唯一入边 |
| `accepts_sound` | `accepts t toks ⟹ ordinary_input ⟹ toks ∈ language G` | 以上 + `parses_derives` + `table_represents_cfg` |

`accepts_sound` 最后一步的形状：
`parses G [Nonterminal (SS G)] (map Terminal toks)` 展开即某条 `(SS G, α) ∈ RR G`
且 `parses G α (map Terminal toks)`，再由 `parses_derives` 得
`derives G [Nonterminal (SS G)] (map Terminal toks)`，即 `toks ∈ language G`。

规模估计：350–450 行。风险：低-中。唯一需要小心的是 `accept_stack_shape`
（见 §2 的 C5/C6 与 §6 的风险 R2）。

### 3.4 `LALR_Completeness.thy`（新增）

**(a) 决定性证书**（在 §2 的 C3/C4 之上，形式化成三条互斥 + 全定义）：

```isabelle
definition lalr_action_determined ::
  "lalr_table ⇒ state_item_map ⇒ state_lookahead_map ⇒ bool" where
  "lalr_action_determined t items lookaheads ⟷
     (∀s tok st. actions t s tok = Some (ActShift st) ⟶
        (∃item ∈ state_items items s. item_symbol_after t item = Some (Terminal tok)) ∧
        (∀rid p. productions t rid = Some p ⟶
           (rid, length (rhs p)) ∈ state_items items s ⟶
           tok ∉ state_item_lookaheads lookaheads s (rid, length (rhs p))))
   ∧ (∀s tok rid. actions t s tok = Some (ActReduce rid) ⟶
        (∃p. productions t rid = Some p ∧ (rid, length (rhs p)) ∈ state_items items s ∧
             tok ∈ state_item_lookaheads lookaheads s (rid, length (rhs p))) ∧
        (∀item ∈ state_items items s. item_symbol_after t item ≠ Some (Terminal tok)))
   ∧ (∀s tok rid1 rid2 p1 p2.
        (rid1, length (rhs p1)) ∈ state_items items s ⟶
        (rid2, length (rhs p2)) ∈ state_items items s ⟶
        tok ∈ state_item_lookaheads lookaheads s (rid1, length (rhs p1)) ⟶
        tok ∈ state_item_lookaheads lookaheads s (rid2, length (rhs p2)) ⟶ rid1 = rid2)"

definition lalr_action_total ::
  "lalr_table ⇒ state_item_map ⇒ state_lookahead_map ⇒ bool" where
  "lalr_action_total t items lookaheads ⟷
     (∀s tok. s ∈ states t ⟶
        ((∃item ∈ state_items items s. item_symbol_after t item = Some (Terminal tok))
         ∨ (∃rid p. productions t rid = Some p ∧ (rid, length (rhs p)) ∈ state_items items s ∧
                   tok ∈ state_item_lookaheads lookaheads s (rid, length (rhs p)))
         ∨ (∃rid p. productions t rid = Some p ∧ item_complete t (rid, length (rhs p)) ∧
                   (rid, length (rhs p)) ∈ state_items items s ∧
                   rhs p = [Nonterminal (SS G)] ∧ tok = end_token))
        ⟶ actions t s tok ≠ None)"
```

**(b) 推导对齐不变量。** 完备性不能用「`S ⇒* 栈 @ 剩余`」（初态不成立），
要用「栈是最右推导当前句型的一个可归约前缀」：

```isabelle
definition aligned :: "symbol cfg ⇒ lalr_table ⇒ token list ⇒ state_item_map ⇒
   state_lookahead_map ⇒ config ⇒ bool" where
  "aligned G t toks items lookaheads cfg ⟷
     (∃σ β. stack_symbols t toks cfg σ ∧
            stack_tracks t items σ (state_stack cfg) ∧
            derives_rm G [Nonterminal (SS G)] (σ @ β) ∧
            β = map Terminal (drop (position cfg) toks) @ β')"
   (* β' 为任意句型：留给 lookahead 语义去约束 *)
```

**(c) 关键引理。**

| 引理 | 内容 | 依赖 |
|---|---|---|
| `handle_at_top` | 若对齐且下一个最右推导步是「把栈顶 `rhs p` 归约成 `lhs p`」，则栈顶状态含完成项 `(rid,|rhs p|)` | `state_items_certificate` 的 reduce 子句 + 追踪 + `stack_items` 迁移 |
| `lookahead_legal` | 该步的 lookahead 属于该完成项的 lookahead 集 | **C2（`lalr_lookahead_sound`）+ FIRST/FOLLOW** |
| `decides` | 于是 `actions t s (lookahead)` 恰为 `Some (ActReduce rid)`（或 shift/accept） | `determined` + `total` + 三个 action 正确性 |
| `step_ok` | 对齐 ∧ 未接受 ⟹ `one_step t cfg = Next cfg'` ∧ `aligned cfg'` | `one_step` 展开 + `decides` |
| `final_accept` | 对齐 ∧ 已到末尾 ⟹ `one_step t cfg = Done (Accepted _)` | accept 正确性 + `decides` |
| `accepts_complete` | `toks ∈ language G ⟹ ordinary_input ⟹ accepts t toks` | 由最右推导归纳构造整条运行；`one_step` 是函数，构造出的运行就是机器唯一的运行 |

**(d) 与终止性的关系。** 完备性**不需要**终止性：构造出的有限运行直接是
`run_rel` 的推导。终止性只在「`recognize fuel` 不返回 `None`」这个推论里用到：
`finite_execution_target` 给出存在有限运行，`run_detailed_fuel_iff_run_rel` 给出对应 fuel。
所以两条线可以并行推进，最后在 `LALR_Equivalence` 汇合。

规模估计：550–800 行。风险：中-高，主要风险在 `lookahead_legal`
（必须先把 FIRST/FOLLOW 的语义与 LALR lookahead 的关系理清）。

### 3.5 `LALR_Equivalence.thy`（新增）

```isabelle
definition lalr_parser_certificate :: ... (* §2 的补强证书打包 *)

theorem accepts_iff_language:
  "lalr_parser_certificate G t items lookaheads bound initial_items ⟹
   ordinary_input t toks ⟹ accepts t toks ⟷ toks ∈ language G"

theorem recognize_iff_language:
  "lalr_parser_certificate G t items lookaheads bound initial_items ⟹
   termination_certificate t toks ⟹ ordinary_input t toks ⟹
   (∃fuel. recognize fuel t toks = Some True) ⟷ toks ∈ language G"

corollary accepts_decidable: "lalr_parser_certificate … ⟹ ordinary_input t toks ⟹
   accepts t toks ∨ ¬ accepts t toks"      (* 平凡，但配合上面即「表是语言的判定过程」 *)
```

规模估计：100–150 行。

---

## 4. 每张表的义务（与终止性格式对齐）

沿用 `LALR_Termination_Schema.thy` 的「固定义务 + 统一入口」风格，语言层同样可以写成一张表：

| 义务 | 路线（可靠性） | 路线（完备性） |
|---|---|---|
| `state_items_certificate`（含 C1 钉死初项） | 需要 | 需要 |
| `lalr_shift/goto/reduce/accept_action_correct` | 需要（reduce/accept 为主） | 需要 |
| C2 `lalr_lookahead_sound` | 不需要 | 需要 |
| C3 `lalr_action_determined` | 不需要 | 需要 |
| C4 `lalr_action_total` | 不需要 | 需要 |
| C5/C6 `state_items_inj`、`start_no_incoming` | 需要（接收形状） | 需要 |
| 终止性（`termination_certificate`） | 仅 fuel 推论需要 | 仅 fuel 推论需要 |

于是每张表要交的东西可以固化成：

```
LALR_Test:      items 映射 + lookaheads + bound + initial_items  （十来个状态的有限表）
                + 5 个证书引理（前三个 by eval，后两个 by simp/auto 的分情况）
                + termination_certificate（已有）
lalr_if_test:   同上（10 状态，含冲突消解：dangling else 的 shift 优先）
complex/SCADE:  同上（表更大，证书数据建议由 Python 生成）
```

**实例化的工程约定**（这是这个仓库已经验证有效的模式，务必沿用）：

1. 证书里的 `∀s ∈ states t`、`∀item ∈ state_items`、`∀tok ∈ terminals t` 全是有限枚举；
   但**不要**指望 `by eval` 直接算 `set`/`Collect` 形式谓词——`LALR_Rank_Auto.thy` 的
   `Wellsortedness error: Type nat × nat not of sort enum` 已经踩过这个坑。
2. 做法：为每个证书写一个**表驱动的布尔检查器**（参数是显式列表：state→item 列表、
   item→lookahead 列表、action 条目列表），先证 `check_X_iff_X`（一次性的等价引理），
   实例处只写 `by eval`。这与 `reduce_rank_check` 完全同构，而且检查器可 `export_code`，
   可以直接和 Python 侧的 `parser.out` 对拍。
3. 更大的表（SCADE）直接让 Python 生成两部分：
   - 表数据 + item/lookahead 数据（Isabelle `definition`，字面列表）；
   - 对应的一串 `lemma … by eval`（检查器逐项判定）。
   再补一条 `by eval` 的「Isabelle 表 ≡ PLY 导出表」的相等性引理，等价性定理就作用于
   **Python 实际使用的那张表**，而不是手抄表。

---

## 5. 里程碑与建议顺序

| 阶段 | 内容 | 产出 | 规模 | 风险 |
|---|---|---|---|---|
| M1 | `LALR_Symbol_Stack` + `LALR_Soundness` | `accepts_sound`（一个方向先落地） | ~600 行 | 低-中 |
| M2 | 算术表（`LALR_Test`）证书数据 + `accepts_sound` 实例 | `test_accepts_sound`，顺带把「证书检查器 + eval」流水线跑通 | ~300 行 | 中（工程性） |
| M3 | `CFG_FIRST_FOLLOW` + `lalr_action_determined/total` + `LALR_Completeness` | `accepts_complete` | ~900 行 | 中-高 |
| M4 | `LALR_Equivalence` + 算术表实例 | `test_accepts_iff_language`、`test_recognize_iff_language` | ~200 行 | 低 |
| M5 | `lalr_if_test` 实例 | dangling-else 表的等价性（顺带验证冲突消解路线） | ~250 行 | 中 |
| M6 | SCADE 表 + PLY 对拍 | 真实模型的语言一致性 | 生成数据 + ~200 行 | 中（数据量） |

建议**先做 M1 + M2**：可靠性的数学内容最干净，且 M2 会立刻暴露「证书数据怎么写、怎么检查」
的工程问题——这类问题在 M3 之前解决，比在完备性证明里同时踩数学和工程的坑要划算。

---

## 6. 风险与备选

**(R1) lookahead 语义（最大风险）。**
`lalr_lookahead_certificate` 目前只说 lookahead ⊆ terminals。完备性需要
「lookahead 合法」以及「FOLLOW 可靠」。两条路：
- 正路：`CFG_FIRST_FOLLOW` 形式化 FIRST/FOLLOW 的最小闭包 + 可靠性，然后
  `lookaheads ⊆ follow` 用 `eval` 检查。教科书内容，但要注意 FIRST 对可空串的处理。
- 备选：把 C2 写成**语义形式**（`can_follow G A tok`，用 `derives` 定义），实例处
  不去证它的一般可靠性，而是对**具体文法**用「FOLLOW 计算 + 有限检查」把它化成
  `tok ∈ follow G A`，再只证 `follow` 的可靠性一次。本质上还是正路，但接口更松，
  允许以后换算法。

**(R2) 接受时的栈形状。**
若真实表的接受状态可以被多条路径到达（状态合并 + 起始状态有入边），
`accept_stack_shape` 不成立，可靠性就会在该点断掉。处理：
- 优先在证书里加 C5/C6（规范构造的表天然满足，`eval` 可查）；
- 若某张真实表不满足（比如手工表），改用更强的语义不变量：把「接受」定义为
  「栈上符号恰好是一个 `S` 的完整派生」——即 `parses G σ (map Terminal toks)` 且 `σ = [S]`，
  这等价于要求表在 accept 时栈高为 2；
- 最后手段：在 `lalr_parser_certificate` 里把「accept 只发生在
  `state_stack = [start_state, acc]`」写成一条**可达性**义务，实例处用「该表所有可达栈形状有限」
  的可执行模拟 + `eval` 检查（对具体表可行，因为状态数少，可用状态对的不动点计算）。

**(R3) ε 产生式。**
现有终止性路线 B 明确排除 ε 归约（`height_reduce_ok_nonempty`）。
可靠性/完备性本身不排除 ε（`pop_rhs 0 stk = Some stk`），但 ε 会让
「合法前缀」与 lookahead 的关系更绕（可空 rhs 的 FIRST）。建议：**等价性定理先只对
无 ε 的文法陈述**（用一个 `no_empty_productions G` 前提），把 ε 作为后续扩展。
本项目三张表都无 ε，不影响交付。

**(R4) 规模与耐心。**
`accepts_complete` 是本方案里唯一「可能反复」的部分。若中途卡住，
可以先把目标降级为
`accepts t toks ⟹ toks ∈ language G`（可靠性）+「完备性对具体文法用有限的
`recognize` 对拍」（不构成定理，只作为工程检验），把等价性留作后续；
但不要在用 `sorry` 的情况下宣称等价性。

---

## 7. 与既有文档的衔接

- `conclusion.md` 第 44 行「尚未证明健全性和完备性」将替换为本文对应的定理名；
- 第 162 行「`generation` 不可满足（`bound = 0`）」的结论保留，但注意它只影响旧的
  `state_items_certificate test_table m 0 {}` 实例；C1 钉死 `initial_items` 后，
  该表应以 `initial_items = {(aug,0)}`、合适的 `bound` 重新实例化（`bound` 只需
  ≥ 最大闭包轮数，取状态数即可）；
- 第 168 行关于 `LALR_Item_Stack.thy` 的 `quick_and_dirty`/`sorry` 已过时（当前无 sorry），
  需要改；
- 新增一节「语言等价性证书」，列出 §4 的义务表与三张表的实例。
