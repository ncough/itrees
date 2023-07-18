theory Sum
  imports ITrees
begin

section \<open>Sum Type\<close>

text \<open>
Building on prior work, a notion of iteration can be introduced given a suitable encoding
of when to progress and when to terminate. This can be encoded within the structure of the
@{type itree}'s result type as a sum, where a left value (@{term Inl}) denotes progress
and a right value (@{term Inr}) denotes termination.
\<close>

abbreviation prog :: "'a \<Rightarrow> ('a+'b,'i,'o) itree"
  where "prog l \<equiv> Ret (Inl l)"

abbreviation exit :: "'b \<Rightarrow> ('a+'b,'i,'o) itree"
  where "exit l \<equiv> Ret (Inr l)"

text \<open>
Due to the frequency with which we interact with an @{type itree} returning a @{type sum},
we introduce a specialised case analysis rule to handle such situations.
\<close>
lemma itree_sum_cases:
  obtains (left) i where "a = prog i" |
          (right) v where "a = exit v" |
          (io) e f where "a = IO e f" |
          (tau) k where "a = Tau k"
  by (cases a, case_tac x1; auto)

subsection \<open>Function Composition over Sum\<close>

text \<open>
We often wish to apply different functions to each side of a sum, so we introduce
the following shorthand to denote such composition.
\<close>

abbreviation case_sum_abv (infix "+\<^sub>f" 55)
  where "case_sum_abv \<equiv> case_sum"

text \<open>
Such composition can be trivially expanded given its application to either @{term prog} or
@{term exit}. Moreover, @{term itree_bind} distributes over this composition.
\<close>
lemma bind_case_sum_simps [itree_simps]:
  "prog i \<bind> a +\<^sub>f b = a i"
  "exit j \<bind> a +\<^sub>f b = b j"
  by (simp add: case_sum_o_inj itree_simps)+

lemma [simp]:
  "prog +\<^sub>f exit = return"
  by (auto simp: surjective_sum)

lemma bind_case_sum_distr  [itree_simps]:
  "itree_bind ((f +\<^sub>f g) i) r = ((\<lambda>i. f i \<bind> r) +\<^sub>f (\<lambda>i. g i \<bind> r)) i"
  by (auto simp: sum.case_eq_if)

lemma bind_cong:
  assumes "a = a'" "\<forall>i. b i = b' i"
  shows "itree_bind a b = a' \<bind> b'"
  using assms by presburger 

lemma case_sum_bind:
  "a \<bind> f +\<^sub>f g \<bind> r = a \<bind> (\<lambda>i. itree_bind (f i) r) +\<^sub>f (\<lambda>i. g i \<bind> r)"
  by (simp add: bind_assoc, rule bind_cong) (auto simp: itree_simps)

subsection \<open>Relation Composition over Sum\<close>

text \<open>
We also introduce a notion of relation composition over a sum, where we assume
both sum's must be of the same side and then apply a corresponding relation.
\<close>

fun case_sum_pred (infix "+\<^sub>p" 100)
  where 
    "case_sum_pred P Q (Inl a) (Inl b) = P a b" |
    "case_sum_pred P Q (Inr a) (Inr b) = Q a b" |
    "case_sum_pred P Q _ _ = False"

lemma [simp]:
  "(((=) +\<^sub>p (=))) = (=)"
  by (auto simp: fun_eq_iff, case_tac x; case_tac xa; auto)

section \<open>Bimap\<close>

text \<open>
A combined mapping over @{type itree} and @{type sum}, useful in a few contexts.
\<close>

definition bimap :: "('a \<Rightarrow> ('b,'c,'d) itree) \<Rightarrow> ('e \<Rightarrow> ('f,'c,'d) itree) \<Rightarrow> ('a + 'e \<Rightarrow> ('b + 'f,'c,'d) itree)"
  where "bimap f g \<equiv> (f ;; prog) +\<^sub>f (g ;; exit)"

lemma [simp]:
  "bimap f g (Inl x) = f x \<bind> prog"
  "bimap f g (Inr y) = g y \<bind> exit"
  by (auto simp: bimap_def)

lemma bimap:
  "bimap f g = (f ;; prog) +\<^sub>f (g ;; exit)"
  unfolding bimap_def by auto

end