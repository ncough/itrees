theory ITrees
  imports Main "HOL-Library.Monad_Syntax"
begin

section \<open>Interaction Trees\<close>

text \<open>
The following is an encoding of interaction trees following the style of earlier work in 
Coq @{cite xia19}. These structures are suitable for describing recursive and potentially
non-terminating programs with uninterpreted interactions with some external environment.
Consequently, they are suitable for the exploration of compiler correctness notions,
as it is possible to describe termination-sensitive notions of equivalence between
programs within an under-specified environment.

Moreover, these structures are internally deterministic.
Non-determinism can be modelled as an interaction with some external oracle that
provides a choice from a finite set of possible inputs.
This constraint may lead to some interesting consequences in modelling security notions,
with which non-determinism is often problematic, but this remains to be explored.

In this section, we define the interaction tree coinductive datatype and define standard
monadic operations over it.
\<close>

text \<open>
An itree consists of three different constructors:
  \<^item> Return, representing termination with a particular value
  \<^item> Tau, representing a silent internal step
  \<^item> IO, consisting of the emission of an event and a continuation to consume the environments
    response to the event  
\<close>
codatatype ('v,'i,'o) itree = 
    Ret 'v 
  | Tau "('v,'i,'o) itree" 
  | IO 'o "('i \<Rightarrow> ('v,'i,'o) itree)"

text \<open>
We introduce a specialised coinductive rule to establish equivalence between itrees,
as case analysis over the left-hand side of the equivalence.
\<close>
lemma itree_coinduct[consumes 1, case_names ret tau io, coinduct type: itree]:
  assumes "P a b"
  assumes "\<And>v a b. P a b \<Longrightarrow> a = Ret v \<Longrightarrow> b = Ret v"
  assumes "\<And>k a b. P a b \<Longrightarrow> a = Tau k \<Longrightarrow> (\<exists>k'. b = Tau k' \<and> (P k k' \<or> k = k'))"
  assumes "\<And>e f a b. P a b \<Longrightarrow> a = IO e f \<Longrightarrow> (\<exists>f'. b = IO e f' \<and> (\<forall>v. P (f v) (f' v) \<or> f v = f' v))"
  shows "a = b"
  using assms(1)
proof (coinduction arbitrary: a b rule: itree.coinduct_strong)
  case Eq_itree
  show ?case
  proof (cases a)
    case (Ret v)
    then show ?thesis using assms(2) Eq_itree by force
  next
    case (Tau k)
    then show ?thesis using assms(3) Eq_itree by force
  next
    case (IO e c)
    then show ?thesis using assms(4) Eq_itree by force
  qed
qed

text \<open>
Coinductive proofs often demand the simplification and destructuring of terms, but this
has to be conducted carefully to avoid infinite recursive expansions.
We remedy this by introducing two collections of simplification and elimination theorems
to be called upon in suitable situations. 
\<close>
named_theorems itree_elims
named_theorems itree_simps

subsection \<open>Monadic Properties\<close>

text \<open>
Interaction tree's are monadic. We first introduce the notion of @{term return},
simply wrapping the @{term Ret} constructor.
\<close>
abbreviation return :: "'v \<Rightarrow> ('v,'i,'o) itree" 
  where 
  "return v \<equiv> Ret v"

text \<open>
Following this, we introduce the notion of bind over @{type itree}s, composing two
@{type itree}s sequentially.
\<close>
primcorec itree_bind :: "('v,'i,'o) itree \<Rightarrow> ('v \<Rightarrow> ('w,'i,'o) itree) \<Rightarrow> ('w,'i,'o) itree" 
  where 
  "itree_bind m f = (case m of Ret v \<Rightarrow> f v
                       | Tau t \<Rightarrow> Tau (itree_bind t f)
                       | IO e g \<Rightarrow> IO e (\<lambda>i. itree_bind (g i) f))"

text \<open>
As syntactic sugar, we introduce a notion of bind for Kleisli composition.
Essentially, compose to functions that return @{type itree}s into one function
that returns an @{type itree}.
\<close>
abbreviation kcomp (infixl ";;" 54) where
  "kcomp a b \<equiv> \<lambda>i. itree_bind (a i) b"

text \<open>
Additional syntactic sugar to denote a single silent step.
\<close>
abbreviation tau where
  "tau \<equiv> \<lambda>i. Tau (Ret i)"

adhoc_overloading Monad_Syntax.bind itree_bind

subsubsection \<open>Deconstruction Properties\<close>

text \<open>
The following simplification and elimination rules allow for the deconstruction of bind terms
in practically all cases. They simply correspond to the an unfolding of the bind definition.
\<close>

lemma bind_simps [itree_simps]:
  "return v \<bind> m = m v"
  "(Tau k) \<bind> m = Tau (k \<bind> m)"
  "(IO e f) \<bind> m = IO e (\<lambda>v. (f v) \<bind> m)"
  by (simp add: itree_bind.code)+

lemma bind_RetE [itree_elims]:
  assumes "m \<bind> f = return v"
  obtains v' where "m = return v'" "f v' = return v"
  using assms by (cases m) (auto simp: itree_simps)

lemma bind_TauE [itree_elims]:
  assumes "m \<bind> f = Tau k"
  obtains (m) k' where "m = Tau k'" "k = k' \<bind> f" |
          (f) v where "m = Ret v" "f v = Tau k"
  using assms by (cases m) (auto simp: itree_simps)

lemma bind_IOE [itree_elims]:
  assumes "m \<bind> f = IO e g"
  obtains (m) g' where "m = IO e g'" "g = (\<lambda>i. (g' i) \<bind> f)" |
          (f) v where "m = Ret v" "f v = IO e g"
  using assms by (cases m) (auto simp: itree_simps)

subsubsection \<open>Monadic Properties\<close>

text \<open>
We demonstrate standard monad laws, first showing that the composition of @{term "itree_bind"} 
and @{term return} is equivalent to @{term id} and second demonstrating the associativity 
of @{term "itree_bind"}.
\<close>
lemma bind_left_id [itree_simps]:
  "a \<bind> return = a"
  by (coinduction arbitrary: a rule: itree_coinduct) (auto elim: itree_elims)

lemma bind_assoc [itree_simps]:
  "bind (itree_bind a b) c = bind a (\<lambda>x. bind (b x) c)"
proof (coinduction arbitrary: a b c rule: itree_coinduct)
  case ret
  then show ?case by (auto elim!: itree_elims simp: bind_simps)
next
  case tau
  then show ?case
    by (auto elim!: itree_elims simp: bind_simps)
       (intro exI conjI, auto simp: bind_simps)+
next
  case io
  then show ?case 
    by (auto elim!: itree_elims simp: bind_simps)
       (intro exI conjI, auto simp: bind_simps)+
qed

subsection \<open>Monadic Map\<close>

text \<open>
Given the notions of @{term return} and @{term "itree_bind"}, we can derive a standard
notion of a map function over the @{type itree}'s result.\<close>

definition itree_fmap :: "('d, 'b, 'c) itree \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('a, 'b, 'c) itree" (infixl "\<oplus>" 60) 
  where 
    "itree_fmap i f \<equiv> i \<bind> (\<lambda>v. return (f v))"

subsubsection \<open>Deconstruction Properties\<close>

text \<open>
We can derive simplification and elimination rules in a similar style to those of 
@{term "itree_bind"}.\<close>

lemma itree_fmap_simps [itree_simps]:
  "Ret v \<oplus> f = Ret (f v)"
  "Tau k \<oplus> f = Tau (k \<oplus> f)"
  "IO e c \<oplus> f = IO e (\<lambda>v. c v \<oplus> f)"
  by (simp add: itree_fmap_def itree_simps)+

lemma itree_fmap_RetE [itree_elims]:
  assumes "m \<oplus> f = Ret v"
  obtains v' where "v = f v'" "m = Ret v'"
  using assms by (cases m; auto simp: itree_simps)

lemma itree_fmap_TauE [itree_elims]:
  assumes "m \<oplus> f = Tau k"
  obtains k' where "k = k' \<oplus> f" "m = Tau k'"
  using assms by (cases m; auto simp: itree_simps)

lemma itree_fmap_IOE [itree_elims]:
  assumes "m \<oplus> f = IO e c"
  obtains c' where "c = (\<lambda>v. c' v \<oplus> f)" "m = IO e c'"
  using assms by (cases m; auto simp: itree_simps)

subsubsection \<open>@{term itree_fmap} Properties\<close>

text \<open>
The @{term itree_fmap} operation shares the identify and composition properties of standard
functions. Moreover, it distributes into a @{term itree_bind}, applying only to its
right-hand side.
\<close>
lemma itree_fmap_props [itree_simps]:
  "m \<oplus> id = m"
  "m \<oplus> f\<^sub>1 \<oplus> f\<^sub>2 = m \<oplus> (f\<^sub>2 o f\<^sub>1)"
  "(m \<bind> c) \<oplus> f = m \<bind> (\<lambda>v. c v \<oplus> f)"
  by (simp add: itree_fmap_def itree_simps)+

subsection \<open>Event Map\<close>

text \<open>
Due to the nature of @{type itree}s, we also introduce a map function over their
environment interactions. This map operation allows for the modification of the
@{type itree}'s emitted events and expected environment responses.

This may be generalised into a form of interpretation of the @{type itree},
in which an "environment" can partially interpret its events, however, this remains to be done.
\<close>

primcorec itree_emap :: "('a, 'b, 'c) itree \<Rightarrow> ('c \<Rightarrow> 'e) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> ('a, 'd, 'e) itree" 
  ("_ \<oplus>\<guillemotleft>_,_\<guillemotright>" [60, 0, 0] 60)
  where
    "itree_emap m ot it = (case m of Ret v \<Rightarrow> Ret v
                                   | Tau k \<Rightarrow> Tau (itree_emap k ot it)
                                   | IO e f \<Rightarrow> IO (ot e) (\<lambda>v. itree_emap (f (it v)) ot it))"

subsubsection \<open>Deconstruction Properties\<close>

text \<open>
Again, we can derive simplification and elimination rules in a similar style to those of 
@{term "itree_bind"}.\<close>

lemma itree_emap_simps [itree_simps]:
  "Ret v \<oplus>\<guillemotleft>ot,it\<guillemotright> = Ret v"
  "Tau k \<oplus>\<guillemotleft>ot,it\<guillemotright> = Tau (k \<oplus>\<guillemotleft>ot,it\<guillemotright>)"
  "IO e c \<oplus>\<guillemotleft>ot,it\<guillemotright> = IO (ot e) (\<lambda>v. c (it v) \<oplus>\<guillemotleft>ot,it\<guillemotright>)"
  by (simp add: itree_emap.code)+

lemma itree_emap_RetE [itree_elims]:
  assumes "m \<oplus>\<guillemotleft>ot,it\<guillemotright> = Ret v"
  obtains "m = Ret v"
  using assms by (cases m; auto simp: itree_simps)

lemma itree_emap_TauE [itree_elims]:
  assumes "m \<oplus>\<guillemotleft>ot,it\<guillemotright> = Tau k"
  obtains k' where "k = k' \<oplus>\<guillemotleft>ot,it\<guillemotright>" "m = Tau k'"
  using assms by (cases m; auto simp: itree_simps)

lemma itree_emap_IOE [itree_elims]:
  assumes "m \<oplus>\<guillemotleft>ot,it\<guillemotright> = IO e c"
  obtains e' c' where "c = (\<lambda>v. c' (it v) \<oplus>\<guillemotleft>ot,it\<guillemotright>)" "m = IO e' c'" "e = ot e'"
  using assms by (cases m; auto simp: itree_simps) 

subsubsection \<open>@{term itree_emap} Properties\<close>

text \<open>
We derive similar properties to those of @{term itree_fmap}, demonstrating the
correspondence with function identify and composition, as well as its
distribution of @{term itree_bind}.
Moreover, we demonstrate that the two map notions are independent.
\<close>
lemma itree_emap_id [itree_simps]:
  "m \<oplus>\<guillemotleft>id,id\<guillemotright> = m"
  by (coinduction arbitrary: m) (auto elim!: itree_elims)

lemma itree_emap_comp [itree_simps]:
  "m \<oplus>\<guillemotleft>ot\<^sub>1,it\<^sub>1\<guillemotright> \<oplus>\<guillemotleft>ot\<^sub>2,it\<^sub>2\<guillemotright> = m \<oplus>\<guillemotleft>ot\<^sub>2 o ot\<^sub>1,it\<^sub>1 o it\<^sub>2\<guillemotright>"
  by (coinduction arbitrary: m) (auto elim!: itree_elims simp: itree_simps)

lemma itree_emap_bind [itree_simps]:
  "(m \<bind> c) \<oplus>\<guillemotleft>ot,it\<guillemotright> = m \<oplus>\<guillemotleft>ot,it\<guillemotright> \<bind> (\<lambda>v. c v \<oplus>\<guillemotleft>ot,it\<guillemotright>)"
  by (coinduction arbitrary: m) (auto elim!: itree_elims simp: itree_simps)

lemma itree_emap_fmap_indep [itree_simps]:
  "m \<oplus> f \<oplus>\<guillemotleft>ot,it\<guillemotright> = m \<oplus>\<guillemotleft>ot,it\<guillemotright> \<oplus> f"
  by (coinduction arbitrary: m) (auto elim!: itree_elims simp: itree_simps)

end