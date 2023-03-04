
(*<*)
theory MyTheory
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Intuicionistička pravila prirodne dedukcije iskazne logike.]\<close>

text \<open>Diskutovati o pravilima uvođenja i pravilima eliminacije prirodne dedukcije iskazne logike.
      Pomoću ključne reči @{text "thm"} ispitati svako pravilo prirodne dedukcije. Primeniti 
      odgovarajuće pravilo prirodne dedukcije na jednostavnim formulama i diskutovati o cilju
      koga treba dokazati pre i posle primene tog pravila.\<close>

text \<open>Uvodjenje konjukcije: \<open>conjI\<close>\<close>

thm conjI

lemma "A \<and> B"
  (*<*) oops (*>*)

text \<open>Uvodjenje disjunkcije: \<open>disjI1\<close>/\<open>disjI2\<close>\<close>

thm disjI1
thm disjI2

lemma "A \<or> B"
  (*<*) oops (*>*)

text \<open>Uvodjenje implikacije: \<open>impI\<close>\<close>

thm impI

lemma "A \<longrightarrow> B"
  (*<*) oops (*>*)

text \<open>Uvodjenje ekvivalencije: \<open>iffI\<close>\<close>

thm iffI

lemma "A \<longleftrightarrow> B"
  (*<*) oops (*>*)

text \<open>Uvodjenje negacije: \<open>notI\<close>\<close>

thm notI

lemma "\<not> A"
  (*<*) oops (*>*)

text \<open>Eliminacija konjukcije. \<open>conjE\<close>\<close>

thm conjE

lemma "A \<and> B \<Longrightarrow> C"
  (*<*) oops (*>*)


text \<open>Eliminacija disjunkcije. \<open>disjE\<close>\<close>

thm disjE

lemma "A \<or> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija implikacije. \<open>impE\<close>\<close>

thm impE

lemma "A \<longrightarrow> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija ekvivalencije. \<open>iffE\<close>\<close>

thm iffE

lemma "A \<longleftrightarrow> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija negacije. \<open>notE\<close>\<close>

thm notE

lemma "\<not> A \<Longrightarrow> B" 
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
