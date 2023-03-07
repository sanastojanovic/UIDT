
(*<*)
theory Vezbe03_resenja
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Intuicionistička pravila prirodne dedukcije u iskaznoj logici]\<close>

text \<open>Diskutovati o pravilima uvođenja i pravilima eliminacije prirodne dedukcije iskazne logike.
      Pomoću ključne reči @{text "thm"} ispitati svako pravilo prirodne dedukcije. Primeniti 
      odgovarajuće pravilo prirodne dedukcije na jednostavnim formulama i diskutovati o cilju
      koga treba dokazati pre i posle primene tog pravila.\<close>

text \<open>Uvodjenje konjukcije: \<open>conjI\<close>\<close>

thm conjI

lemma "A \<and> B"
  apply (rule conjI)
  (*<*) oops (*>*)

text \<open>Uvodjenje disjunkcije: \<open>disjI1\<close>/\<open>disjI2\<close>\<close>

thm disjI1
thm disjI2

lemma "A \<or> B"
  apply (rule disjI2)
  (*<*) oops (*>*)

text \<open>Uvodjenje implikacije: \<open>impI\<close>\<close>

thm impI

lemma "A \<longrightarrow> B"
  apply (rule impI)
  (*<*) oops (*>*)

text \<open>Uvodjenje ekvivalencije: \<open>iffI\<close>\<close>

thm iffI

lemma "A \<longleftrightarrow> B"
  apply (rule iffI)
  (*<*) oops (*>*)

text \<open>Uvodjenje negacije: \<open>notI\<close>\<close>

thm notI

lemma "\<not> A"
  apply (rule notI)
  (*<*) oops (*>*)

text \<open>Eliminacija konjukcije. \<open>conjE\<close>\<close>

thm conjE

lemma "A \<and> B \<Longrightarrow> C"
  apply (erule conjE)
  (*<*) oops (*>*)


text \<open>Eliminacija disjunkcije. \<open>disjE\<close>\<close>

thm disjE

lemma "A \<or> B \<Longrightarrow> C"
  apply (erule disjE)
  (*<*) oops (*>*)

text \<open>Eliminacija implikacije. \<open>impE\<close>\<close>

thm impE

lemma "A \<longrightarrow> B \<Longrightarrow> C"
  apply (erule impE)
  (*<*) oops (*>*)

text \<open>Eliminacija ekvivalencije. \<open>iffE\<close>\<close>

thm iffE

lemma "A \<longleftrightarrow> B \<Longrightarrow> C"
  apply (erule iffE)
  (*<*) oops (*>*)

text \<open>Eliminacija negacije. \<open>notE\<close>\<close>

thm notE

lemma "\<not> A \<Longrightarrow> B" 
  apply (erule notE)
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Dokazi u prirodnoj dedukciji]\<close>

text \<open>Pokazati da su sledeće formule tautologija u iskaznoj logici. 
      Dozvoljeno je korišćenje samo intuicionističkih pravila prirodne dedukcije.\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption +
  done

lemma "A \<or> B \<longrightarrow> B \<or> A"
  apply (rule impI)
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done

lemma "A \<and> B \<longrightarrow> A \<or> B"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
  done

lemma "(A \<and> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  apply (rule impI) +
  apply (erule impE)
   apply (rule conjI)
    apply assumption +
  done

lemma "(A \<longrightarrow> (B \<longrightarrow> C)) \<longrightarrow> (A \<and> B \<longrightarrow> C)"
  apply (rule impI) +
  apply (erule impE)
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply (erule impE)
   apply assumption +
  done

lemma "\<not> (A \<or> B) \<longrightarrow> \<not> A \<and> \<not> B"
  apply (rule impI)
  apply (rule conjI)
   apply (rule notI)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

lemma "\<not> A \<and> \<not> B \<longrightarrow> \<not> (A \<or> B)"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply (erule notE) +
  apply assumption
  done

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE) back
   apply (rule notI)
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

text \<open>Dodatni primeri\<close>

lemma "(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)"
  apply (rule impI)
  apply (rule iffI)
   apply (erule conjE) +
   apply (erule impE) back back
    apply assumption
   apply (erule disjE)
    apply assumption
   apply (erule impE) back
    apply assumption
   apply (erule conjE)
   apply assumption
  apply (erule conjE) +
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

lemma "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<and> R)"
  apply (rule impI) +
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (rule conjI)
   apply assumption
  apply (erule impE)
   apply assumption +
  done

lemma "(P \<longrightarrow> Q) \<and> \<not> Q \<longrightarrow> \<not> P"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done


lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> (Q \<longrightarrow> (P \<longrightarrow> R))"
  apply (rule impI) +
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption +
  done

lemma "\<not> (P \<and> \<not>P)"
  apply (rule notI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done

lemma "A \<and> (B \<or> C ) \<longrightarrow> (A \<and> B) \<or> (A \<and> C)"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule conjI)
    apply assumption +
  apply (rule disjI2)
  apply (rule conjI)
  apply assumption +
  done

lemma "\<not> (A \<and> B) \<longrightarrow> (A \<longrightarrow> \<not> B)"
  apply (rule impI) +
  apply (rule notI)
  apply (erule notE)
  apply (rule conjI)
   apply assumption +
  done

lemma "(A \<longrightarrow> C ) \<and> (B \<longrightarrow> \<not> C ) \<longrightarrow> \<not> (A \<and> B)"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE) +
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(A \<and> B) \<longrightarrow> ((A \<longrightarrow> C ) \<longrightarrow> \<not> (B \<longrightarrow> \<not> C ))"
  apply (rule impI) +
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(A \<longleftrightarrow> B) \<longrightarrow> (\<not> A \<longleftrightarrow> \<not> B)"
  apply (rule impI)
  apply (erule iffE)
  apply (rule iffI)
   apply (rule notI)
   apply (erule impE) back
    apply assumption
   apply (erule notE)
   apply assumption
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "A \<longrightarrow> \<not> \<not> A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE) back
   apply (rule notI)
   apply (erule impE)
    apply assumption
  apply (erule notE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> \<not> A)"
  apply (rule impI) +
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "\<not> A \<or> B \<longrightarrow> (A \<longrightarrow> B)"
  apply (rule impI) +
  apply (erule disjE)
   apply (erule notE)
   apply assumption +
  done

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
