
(*<*)
theory Vezbe02_resenja
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Zapisivanje logičkih formula (nastavak)]\<close>

text \<open>(a) Zapisati sledeće rečenice u logici prvog reda i dokazati njihovu ispravnost.\<close>

text \<open>(a.1) Ako ”šta leti to ima krila i lagano je” 
            i ”šta pliva, to nema krila”, 
            onda ”šta pliva, to ne leti”\<close>

lemma "
    (\<forall> x. Leti x \<longrightarrow> Krila x \<and> Lagano x) \<and>
    (\<forall> x. Pliva x \<longrightarrow> \<not> Krila x) \<longrightarrow>
    (\<forall> x. Pliva x \<longrightarrow> \<not> Leti x)"
  by auto

text \<open>(a.2) Ako postoji cipela koja u svakom trenutku odgovara svakoj nozi, 
            onda za svaku nogu postoji cipela koja joj u nekom trenutku odgovara 
            i za svaku nogu postoji trenutak takav da postoji cipela koja joj u tom 
            trenutku odgovara.\<close>

lemma "
    (\<exists> cipela. \<forall> trenutak. \<forall> noga. Odgovara cipela trenutak noga) \<longrightarrow>
    (\<forall> noga. \<exists> cipela. \<exists> trenutak. Odgovara cipela trenutak noga) \<and>
    (\<forall> noga. \<exists> trenutak. \<exists> cipela. Odgovara cipela trenutak noga)"
  by auto


text \<open>(b) Pokazati da je rečenica P logička posledica rečenica P1, P2, P3.\<close>

text \<open>P:  Andrija voli da pleše.\<close>
text \<open>P1: Svako ko je srećan voli da peva.\<close>
text \<open>P2: Svako ko voli da peva, voli da pleše.\<close>
text \<open>P3: Andrija je srećan.\<close>

lemma "
    (\<forall> x. Srecan x \<longrightarrow> Peva x) \<and>
    (\<forall> x. Peva x \<longrightarrow> Plese x) \<and>
    Srecan Andrija \<longrightarrow>
    Plese Andrija"
  by auto

text \<open>P':  Svako dete voli da se igra.\<close>
text \<open>P1': Svaki dečak voli da se igra.\<close>
text \<open>P2': Svaka devojčica voli da se igra.\<close> 
text \<open>P3': Dete je dečak ili je devojčica.\<close>

lemma "
    (\<forall> x. Decak x \<longrightarrow> Igra x) \<and>
    (\<forall> x. Devojcica x \<longrightarrow> Igra x) \<and>
    (\<forall> x. Dete x \<longrightarrow> Decak x \<or> Devojcica x) \<longrightarrow>
    (\<forall> x. Dete x \<longrightarrow> Igra x) "
  by auto

text \<open>(c) Na jeziku logike prvog reda zapisati sledeće rečenice i dokazati da su skupa nezadovoljive.\<close>

text \<open>- Svaka dva brata imaju zajedničkog roditelja.\<close>
text \<open>- Roditelj je stariji od deteta.\<close>
text \<open>- Postoje braća.\<close>
text \<open>- Nijedna osoba nije starija od druge.\<close>

lemma "
    (\<forall> x. \<forall> y. \<exists> z. Brat x y \<longrightarrow> Roditelj x z \<and> Roditelj y z) \<and>
    (\<forall> x. \<forall> y. Roditelj x y \<longrightarrow> Stariji y x) \<and>
    (\<exists> x. \<exists> y. Brat x y) \<and>
    (\<not> (\<exists> x. \<exists> y. Stariji x y)) \<longrightarrow> 
    False"
  by auto

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Silogizmi]\<close>

text \<open>Barbara (AAA-1)\<close>
text \<open>All men are mortal. (MaP)\<close>
text \<open>All Greeks are men. (SaM)\<close>
text \<open>— All Greeks are mortal. (SaP)\<close>
(*<*)
lemma Barbara: "undefined"
  oops (*>*)

lemma Barbara: "
    (\<forall> x. Man x \<longrightarrow> Mortal x) \<and>
    (\<forall> x. Greek x \<longrightarrow> Man x) \<longrightarrow>
    (\<forall> x. Greek x \<longrightarrow> Mortal x)"
  by auto

text \<open>Celarent (EAE-1)\<close>
text \<open>Similar: Cesare (EAE-2)\<close>
text \<open>No reptiles have fur. (MeP)\<close>
text \<open>All snakes are reptiles. (SaM)\<close>
text \<open>— No snakes have fur. (SeP)\<close>
(*<*)
lemma Celarent: "undefined" 
  oops (*>*)

lemma Celarent: "
    (\<not> (\<exists> x. Reptile x \<and> Fur x)) \<and>
    (\<forall> x. Snake x \<longrightarrow> Reptile x) \<longrightarrow>
    (\<not> (\<exists> x. Snake x \<and> Fur x))"
  by auto


text \<open>Ferioque (EIO-1)\<close>
text \<open>No homework is fun. (MeP)\<close>
text \<open>Some reading is homework. (SiM)\<close>
text \<open>— Some reading is not fun. (SoP)\<close>

(*<*)
lemma Ferioque: "undefined"
  oops (*>*)

lemma Ferioque: "
    (\<not> (\<exists> x. Homework x \<longrightarrow> Fun x)) \<and>
    (\<exists> x. Reading x \<and> Homework x) \<longrightarrow>
    (\<exists> x. Reading x \<and> \<not> Fun x)"
  by auto

text \<open>Bocardo (OAO-3)\<close>
text \<open>Some cats are not pets. (MoP)\<close>
text \<open>All cats are mammals. (MaS)\<close>
text \<open>— Some mammals are not pets. (SoP)\<close>
(*<*)
lemma Bocardo: "undefined"
  oops (*>*)

lemma Bocardo: "
    (\<exists> x. Cat x \<and> \<not>Pet x) \<and>
    (\<forall> x. Cat x \<longrightarrow> Mammal x) \<longrightarrow>
    (\<exists> x. Mammal x \<and> \<not>Pet x)"
  by auto

text \<open>Barbari (AAI-1)\<close>
text \<open>All men are mortal. (MaP)\<close>
text \<open>All Greeks are men. (SaM)\<close>
text \<open>— Some Greeks are mortal. (SiP)\<close>
(*<*)
lemma Barbari: "undefined"
  oops (*>*)

lemma Barbari: "
    (\<forall> x. Man x \<longrightarrow> Mortal x) \<and>
    (\<forall> x. Greek x \<longrightarrow> Man x) \<and>
    (\<exists> x. Greek x) \<longrightarrow>
    (\<exists> x. Greek x \<and> Mortal x)"
  by auto

text \<open>Celaront (EAO-1)\<close>
text \<open>No reptiles have fur. (MeP)\<close>
text \<open>All snakes are reptiles. (SaM)\<close>
text \<open>— Some snakes have no fur. (SoP)\<close>
(*<*)
lemma Celaront: "undefined"
  oops (*>*)

lemma Celaront: "
    (\<not> (\<exists> x. Reptile x \<and> Fur x)) \<and>
    (\<forall> x. Snake x \<longrightarrow> Reptile x) \<and>
    (\<exists> x. Snake x) \<longrightarrow>
    (\<exists> x. Snake x \<and> \<not>Fur x)"
  by auto

text \<open>Camestros (AEO-2)\<close>
text \<open>All horses have hooves. (PaM)\<close>
text \<open>No humans have hooves. (SeM)\<close>
text \<open>— Some humans are not horses. (SoP)\<close>
(*<*)
lemma Camestros: "undefined"
  oops (*>*)

lemma Camestros: "
    (\<forall> x. Horse x \<longrightarrow> Hooves x) \<and>
    (\<not> (\<exists> x. Human x \<and> Hooves x)) \<and>
    (\<exists> x. Human x) \<longrightarrow>
    (\<exists> x. Human x \<and> \<not>Horse x)"
  by auto

text \<open>Felapton (EAO-3)\<close>
text \<open>No flowers are animals. (MeP)\<close>
text \<open>All flowers are plants. (MaS)\<close>
text \<open>— Some plants are not animals. (SoP)\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Raymond M. Smullyan: Logical Labyrinths]\<close>

text \<open>Edgar Aberkrombi je bio antropolog koji se interesovao za logiku i socijologiju
      laganja i govorenja istine. Jednog dana je odlučio da poseti ostrvo vitezova i podanika.
      Stanovnike ovog ostrva delimo na one koji uvek govore istinu @{text "vitezove"} i
      one koji uvek govore laži @{text "podanike"}. Dodatno, na ostrvu žive samo vitezovi i 
      podanici. Aberkrombi susreće stanovnike i želi da prepozna ko je od njih vitez, 
      a ko je podatnik.\<close>

text \<open>1. Svaka osoba će odgovoriti potvrdno na pitanje: Da li si ti vitez?\<close>

lemma no_one_admit_knaves: 
  assumes "k \<longleftrightarrow> (k \<longleftrightarrow> yes)"
  shows "yes"
  using assms
  by auto

text \<open>1.1 Aberkombi je razgovarao sa tri stanovnika ostrva, označimo ih sa A, B i C. 
          Pitao je stanovnika A: ”Da li si ti vitez ili podanik?” 
          A je odgovorio ali nerazgovetno 
          pa je Aberkombi pitao stanovnika B: ”Šta je A rekao?” 
          B je odgovorio: ”Rekao je da je on podanik.” 
          Tada se uključila i osoba C i rekla: ”Ne veruj mu, on laže!” 
          Da li je osoba C vitez ili podanik?\<close>

lemma Smullyan_1_1:
  assumes "kA \<longleftrightarrow> (kA \<longleftrightarrow> yesA)"
      and "kB \<longleftrightarrow> \<not> yesA"
      and "kC \<longleftrightarrow> \<not> kB"
    shows "kC"
  using assms
  by auto
 

text \<open>1.2 Aberkombi je pitao 
          stanovnika A koliko među njima trojicom ima podanika. 
          A je opet odgovorio nerazgovetno,
          tako da je Aberkombi pitao stanovnika B šta je A rekao. 
          B je rekao da je A rekao da su tačno dvojica podanici. 
          Ponovo je stanovnik C tvrdio da B laže. 
          Da li je u ovoj situaciji moguće odrediti da li je C vitez ili podanik?\<close>

definition exactly_two :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "exactly_two x y z \<longleftrightarrow> ((x \<and> y) \<or> (y \<and> z) \<or> (z \<and> x)) \<and> \<not> (x \<and> y \<and> z)"

lemma Smullyan_1_2:
  assumes "kA \<longleftrightarrow> (exactly_two (\<not> kA) (\<not> kB) (\<not> kC) \<longleftrightarrow> yesA)"
      and "kB \<longleftrightarrow> yesA"
      and "kC \<longleftrightarrow> \<not> kB"
    shows "kC"
  using assms
  unfolding exactly_two_def
  by auto

text \<open>1.3 Da li se zaključak prethodnog tvrđenja menja ako B promeni svoj odgovor 
          i kaže da je A rekao da su tačno dva od njih vitezovi?\<close>

lemma Smullyan_1_3:
  assumes "kA \<longleftrightarrow> (exactly_two kA kB kC \<longleftrightarrow> yesA)"
      and "kB \<longleftrightarrow> yesA"
      and "kC \<longleftrightarrow> \<not> kB"
    shows "\<not> kC"
  using assms
  unfolding exactly_two_def
  by auto

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
