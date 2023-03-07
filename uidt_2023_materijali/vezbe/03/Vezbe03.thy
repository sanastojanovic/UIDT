
(*<*)
theory Vezbe03
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Intuicionistička pravila prirodne dedukcije u iskaznoj logici]\<close>

text \<open>Diskutovati o pravilima uvođenja i pravilima eliminacije prirodne dedukcije iskazne logike.
      Pomoću ključne reči @{text "thm"} ispitati svako pravilo prirodne dedukcije. Primeniti 
      odgovarajuće pravilo prirodne dedukcije na jednostavnim formulama i diskutovati o cilju
      koga treba dokazati pre i posle primene tog pravila.\<close>

text \<open>Uvodjenje konjukcije: \<open>conjI\<close>\<close>

lemma "A \<and> B"
  (*<*) oops (*>*)

text \<open>Uvodjenje disjunkcije: \<open>disjI1\<close>/\<open>disjI2\<close>\<close>

lemma "A \<or> B"
  (*<*) oops (*>*)

text \<open>Uvodjenje implikacije: \<open>impI\<close>\<close>

lemma "A \<longrightarrow> B"
  (*<*) oops (*>*)

text \<open>Uvodjenje ekvivalencije: \<open>iffI\<close>\<close>

lemma "A \<longleftrightarrow> B"
  (*<*) oops (*>*)

text \<open>Uvodjenje negacije: \<open>notI\<close>\<close>

lemma "\<not> A"
  (*<*) oops (*>*)

text \<open>Eliminacija konjukcije. \<open>conjE\<close>\<close>

lemma "A \<and> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija disjunkcije. \<open>disjE\<close>\<close>

lemma "A \<or> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija implikacije. \<open>impE\<close>\<close>

lemma "A \<longrightarrow> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija ekvivalencije. \<open>iffE\<close>\<close>

lemma "A \<longleftrightarrow> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija negacije. \<open>notE\<close>\<close>

lemma "\<not> A \<Longrightarrow> B" 
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Dokazi u prirodnoj dedukciji]\<close>

text \<open>Pokazati da su sledeće formule tautologija u iskaznoj logici. 
      Dozvoljeno je korišćenje samo intuicionističkih pravila prirodne dedukcije.\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
  (*<*) oops (*>*)

lemma "A \<or> B \<longrightarrow> B \<or> A"
  (*<*) oops (*>*)

lemma "A \<and> B \<longrightarrow> A \<or> B"
  (*<*) oops (*>*)

lemma "(A \<and> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  (*<*) oops (*>*)

lemma "(A \<longrightarrow> (B \<longrightarrow> C)) \<longrightarrow> (A \<and> B \<longrightarrow> C)"
  (*<*) oops (*>*)

lemma "\<not> (A \<or> B) \<longrightarrow> \<not> A \<and> \<not> B"
  (*<*) oops (*>*)

lemma "\<not> A \<and> \<not> B \<longrightarrow> \<not> (A \<or> B)"
  (*<*) oops (*>*)

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  (*<*) oops (*>*)

text \<open>Dodatni primeri:\<close>

lemma "(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)"
  (*<*) oops (*>*)

lemma "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<and> R)"
  (*<*) oops (*>*)

lemma "(P \<longrightarrow> Q) \<and> \<not> Q \<longrightarrow> \<not> P"
  (*<*) oops (*>*)

lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> (Q \<longrightarrow> (P \<longrightarrow> R))"
  (*<*) oops (*>*)

lemma "\<not> (P \<and> \<not>P)"
  (*<*) oops (*>*)

lemma "A \<and> (B \<or> C ) \<longrightarrow> (A \<and> B) \<or> (A \<and> C)"
  (*<*) oops (*>*)

lemma "\<not> (A \<and> B) \<longrightarrow> (A \<longrightarrow> \<not> B)"
  (*<*) oops (*>*)

lemma "(A \<longrightarrow> C ) \<and> (B \<longrightarrow> \<not> C ) \<longrightarrow> \<not> (A \<and> B)"
  (*<*) oops (*>*)

lemma "(A \<and> B) \<longrightarrow> ((A \<longrightarrow> C ) \<longrightarrow> \<not> (B \<longrightarrow> \<not> C ))"
  (*<*) oops (*>*)

lemma "(A \<longleftrightarrow> B) \<longrightarrow> (\<not> A \<longleftrightarrow> \<not> B)"
  (*<*) oops (*>*)

lemma "A \<longrightarrow> \<not> \<not> A"
  (*<*) oops (*>*)

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  (*<*) oops (*>*)

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> \<not> A)"
  (*<*) oops (*>*)

lemma "\<not> A \<or> B \<longrightarrow> (A \<longrightarrow> B)"
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
