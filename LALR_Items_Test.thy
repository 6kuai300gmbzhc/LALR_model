theory LALR_Items_Test
  imports LALR_Test
begin

text \<open>
  M2 groundwork: the LR(0) item-set algebra needed to discharge
  @{text state_items_certificate}.  A superset that is closed under
  @{text item_closure_step} absorbs the whole closure iteration.
\<close>

lemma item_closure_step_mono:
  "A \<subseteq> B \<Longrightarrow> item_closure_step t A \<subseteq> item_closure_step t B"
  unfolding item_closure_step_def by blast

lemma item_closure_step_self: "A \<subseteq> item_closure_step t A"
  unfolding item_closure_step_def by blast

lemma item_closure_iter_mono:
  "A \<subseteq> B \<Longrightarrow> item_closure_iter t n A \<subseteq> item_closure_iter t n B"
proof (induct n arbitrary: A B)
  case 0
  then show ?case by (auto simp: item_closure_iter.simps)
next
  case (Suc n)
  have step: "item_closure_step t A \<subseteq> item_closure_step t B"
    using Suc(2) by (rule item_closure_step_mono)
  from Suc(1)[OF step] show ?case by (simp add: item_closure_iter.simps)
qed

lemma item_closure_iter_subset_closed:
  "A \<subseteq> B \<Longrightarrow> item_closure_step t B \<subseteq> B \<Longrightarrow> item_closure_iter t n A \<subseteq> B"
proof (induct n arbitrary: A)
  case 0
  then show ?case by (auto simp: item_closure_iter.simps)
next
  case (Suc n)
  have step_sub: "item_closure_step t A \<subseteq> B"
    using Suc(2) Suc(3) by (metis item_closure_step_mono subset_trans)
  from Suc(1)[OF step_sub Suc(3)] show ?case by (simp add: item_closure_iter.simps)
qed

lemma item_closure_iter_inc: "A \<subseteq> item_closure_iter t n A"
proof (induct n)
  case 0
  then show ?case by (auto simp: item_closure_iter.simps)
next
  case (Suc n)
  have ih: "A \<subseteq> item_closure_iter t n A" using Suc by simp
  have mono: "item_closure_iter t n A \<subseteq> item_closure_iter t n (item_closure_step t A)"
    by (rule item_closure_iter_mono, rule item_closure_step_self)
  have mid: "A \<subseteq> item_closure_iter t n (item_closure_step t A)"
    using ih mono by (rule subset_trans)
  show ?case by (metis item_closure_iter.simps(2) mid)
qed

lemma item_closure_step_subset_iter:
  "0 < n \<Longrightarrow> item_closure_step t A \<subseteq> item_closure_iter t n A"
proof -
  assume "0 < n"
  then obtain m where n_eq: "n = Suc m" by (cases n) auto
  have step_inc: "item_closure_step t A \<subseteq> item_closure_iter t m (item_closure_step t A)"
    by (rule item_closure_iter_inc)
  show ?thesis by (metis item_closure_iter.simps(2) n_eq step_inc)
qed

end
