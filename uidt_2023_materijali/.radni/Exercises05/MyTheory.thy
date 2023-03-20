
(*<*)
theory MyTheory
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Algebra skupova]\<close>

text \<open>Diskutovati o sledećim termovima:\<close>

term "{1, 2, 3}"
term "{1::nat, 2, 3}"
term "(\<in>)"
term "(\<inter>)"
term "(\<union>) A"
term "(A::'a set) - B"

text_raw \<open> \end{exercise} \<close>


text_raw \<open>\begin{exercise}[subtitle=Isar dokazi]\<close>

text \<open>Pokazati sledeća tvrđenja o skupovima pomoću jezika Isar.\<close>

text \<open>\<open>Napomena\<close>: Dozvoljeno je korišćenje samo \<open>simp\<close> metode za
                  dokazivanje pojedinačnih koraka.\<close>

lemma "- (A \<union> B) = - A \<inter> - B"
  (*<*) oops (*>*)

text \<open>\<open>Savet\<close>: Iskoristiti @{text "find_theorems _ \<or> _ \<longleftrightarrow> _ \<or> _"} 
               za pronalaženje odgovarajuće teoreme.\<close>

lemma "A \<union> B = B \<union> A"
proof
  show "A \<union> B \<subseteq> B \<union> A"
  proof
    fix x
    assume "x \<in> A \<union> B"
    show "x \<in> B \<union> A"
     (*<*) sorry (*>*)
  qed
next
  show "B \<union> A \<subseteq> A \<union> B"
    (*<*) sorry (*>*)
qed

text \<open>\<open>Savet\<close>: Iskoristiti aksiomu isključenja trećeg @{text "A \<or> \<not>A"}
               u kontekstu operacije pripadanja @{text "(\<in>) :: 'a \<Rightarrow> 'a set \<Rightarrow> bool"}.\<close>

lemma "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)" (is "?left = ?right")
proof
  show "?left \<subseteq> ?right"
  (*<*) sorry (*>*)
next
  show "?right \<subseteq> ?left"
  (*<*) sorry (*>*)
qed

lemma "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)" (is "?left = ?right")
  (*<*) oops (*>*)

lemma "A - (B \<inter> C ) = (A - B) \<union> (A - C )" (is "?left = ?right")
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
