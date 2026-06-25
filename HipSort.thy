theory HipSort
  imports Main "HOL-Library.Multiset"
begin

definition swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "swap l i j = l[i := l ! j, j := l ! i]"

fun roditelj :: "nat \<Rightarrow> nat" where
  "roditelj i = (i - 1) div 2"

fun levo :: "nat \<Rightarrow> nat" where
  "levo i = 2*i + 1"

fun desno :: "nat \<Rightarrow> nat" where
  "desno i = 2*i + 2"

lemma mset_swap [simp]: 
assumes "i < length l"
and "j < length l"
shows "mset (swap l i j) = mset l"
  using assms
  unfolding swap_def 
  by (metis mset_swap)

(*grupa ubaci*)
fun ubaci :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"ubaci l i = 
   (if i = 0 then 
        l 
    else
       (if l ! (roditelj i) \<ge> l ! i then
            l
        else
            ubaci (swap l i (roditelj i)) (roditelj i)))"

(*grupa ubaci*)
function ubaciSve :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"ubaciSve l i = (if i \<ge> length l then l else ubaciSve (ubaci l i) (i+1))"
  by pat_completeness auto
termination
  sorry

fun najveci3 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"najveci3 l i m = 
   (if desno i < m then
       (if l!i >= l!levo i \<and> l!i >= l!desno i then 
            i
        else if l!levo i >= l!desno i then
            levo i
        else 
            desno i
       )
    else if levo i < m then 
        (if (l!i) \<ge> (l!levo i) then
            i 
         else 
            levo i
        ) 
    else 
         i
    )"

(*grupa izbaci*)
function izbaci :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list" where
"izbaci l i m = (let najveci = najveci3 l i m in 
    (if i = najveci then l
         else izbaci (swap l i najveci) najveci m))"
  by pat_completeness auto
termination
  sorry

(*grupa izbaci*)
fun izbaciSve :: "int list \<Rightarrow> nat \<Rightarrow> int list" where
"izbaciSve l i = (if i = 0 then l else izbaciSve (izbaci (swap l 0 (i-1)) 0 (i-1)) (i-1))"

fun HipSort :: "int list \<Rightarrow> int list" where
"HipSort l = izbaciSve (ubaciSve l 0) (length l)"

(*grupa ubaci*)
fun JesteHip1 :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteHip1 l m = (\<forall>i \<in> {1..<m}. l!roditelj i \<ge> l!i)"

(*grupa izbaci*)
fun JesteHip2 :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteHip2 l m = (\<forall>i \<in> {0..<m}. i = najveci3 l i m)"

lemma l2to1:
  assumes "0 < i"
  and "i < m"
  and "najveci3 l (roditelj i) m = roditelj i"
  shows "l ! i \<le> l ! roditelj i"
proof (cases "2 dvd i")
  case True
  have "roditelj i < m"
      using assms
      by (metis One_nat_def Suc_leI True add_Suc_right diff_le_self div_less_dividend lessI nat_arith.rule0
          nat_dvd_not_less nat_less_le one_add_one order_less_le_trans roditelj.simps zero_less_diff)
    then have "roditelj i = najveci3 l (roditelj i) m"
      using assms
      by auto
    moreover
    have "i = desno (roditelj i)"
      using assms True
      by (metis One_nat_def Suc_pred add.commute add_gr_0 desno.elims div2_Suc_Suc dvdE even_Suc_div_two lessI
          mult_Suc_right nat_less_le nonzero_mult_div_cancel_left one_add_one roditelj.simps)
    ultimately show ?thesis
      by (smt (verit, ccfv_SIG) assms najveci3.simps)
next
  case False
  have "roditelj i < m"
    using assms
    by (metis (no_types, lifting) One_nat_def Suc_le_eq Suc_pred add_Suc_right div_less div_less_dividend
        linorder_not_less nat_arith.rule0 nat_less_le one_add_one order_less_le_trans roditelj.simps)
  then have "roditelj i = najveci3 l (roditelj i) m"
    using assms
    by metis
  moreover
  have "i = levo (roditelj i)"
    using assms False
    by auto
  ultimately show ?thesis
    by (smt (verit, ccfv_SIG) assms najveci3.simps)
qed

lemma najveci3slucaj1:
  assumes "desno i < m"
  shows "(najveci3 l i m = i) \<longleftrightarrow> (l!i \<ge> l!levo i \<and> l!i \<ge> l!desno i)"
  using assms
  by auto

lemma najveci3slucaj2:
  assumes "desno i = m"
  shows "(najveci3 l i m = i) \<longleftrightarrow> (l!i \<ge> l!levo i)"
  using assms
  by auto

lemma najveci3slucaj3:
  assumes "desno i > m"
  shows "najveci3 l i m = i"
  using assms
  by auto

lemma l1to2:
  assumes "(desno i < m \<and> l!i \<ge> l!levo i \<and> l!i \<ge> l!desno i) \<or> (desno i = m \<and> l!i \<ge> l!levo i) \<or> (desno i > m)"
  shows "najveci3 l i m = i"
  using assms
  by auto

lemma JesteHipEquivDef: "JesteHip1 l m = JesteHip2 l m"
proof
  assume "JesteHip1 l m"
  then have *: "\<forall>i. (0 < i \<and> i < m) \<longrightarrow> l!(roditelj i) \<ge> l!i"
    by auto
  have "\<forall>i. i < m \<longrightarrow> i = najveci3 l i m"
  proof 
    fix i::nat

    show "i < m \<longrightarrow> i = najveci3 l i m "
      using * l1to2
      by auto
  qed
  then show "JesteHip2 l m"
    by auto
next
  assume "JesteHip2 l m"
  then have *: "\<forall>i. i < m \<longrightarrow> i = najveci3 l i m"
    by auto
  have "\<forall>i. (0 < i \<and> i < m) \<longrightarrow> l!(roditelj i) \<ge> l!i"
  proof
    fix i::nat

    show "0 < i \<and> i < m \<longrightarrow> l ! i \<le> l ! roditelj i"
      using l2to1 *
      by auto
  qed
  then show "JesteHip1 l m"
    by auto
qed

fun najveci3roditelj :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"najveci3roditelj l i m = 
   (if desno i < m then
       (if l!roditelj i \<ge> l!levo i \<and> l!roditelj i \<ge> l!desno i then 
            roditelj i
        else if l!levo i \<ge> l!desno i then
            levo i
        else 
            desno i
       )
    else if levo i < m then 
        (if (l!roditelj i) \<ge> (l!levo i) then
            roditelj i
         else 
            levo i
        ) 
    else 
         roditelj i
    )"

(*grupa ubaci*)
fun SkoroHip1 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"SkoroHip1 l m q = ((\<forall>i \<in> {1..<m} - {q}. l!roditelj i \<ge> l!i) \<and> najveci3roditelj l q m = roditelj q)"

(*grupa izbaci*)
fun SkoroHip2 :: "int list \<Rightarrow> nat  \<Rightarrow> nat \<Rightarrow> bool" where
"SkoroHip2 l m q = (\<forall>i \<in> {0..<m} - {q}. i = najveci3 l i m)"

lemma VezaSkoroJeste2: "2*q + 1 > m \<and> SkoroHip2 l m q \<longrightarrow> JesteHip2 l m"
proof
  assume *: "m < 2 * q + 1 \<and> SkoroHip2 l m q"
  from * have "\<forall>i \<in> {0..<m} - {q}. i = najveci3 l i m"
    by auto
  moreover
  from * have "q = najveci3 l q m"
    by auto
  ultimately show "JesteHip2 l m"
    by (metis JesteHip2.elims(3) insert_iff insert_Diff_single)
qed

fun JesteSortiran :: "int list \<Rightarrow> nat \<Rightarrow> bool" where
"JesteSortiran l m = sorted (drop m l)"

value "JesteHip [9, 3, 8, 2, 3, 8, 8, 1, 2, 3, 1, 8] 10"
value "najveci3 [9, 3, 7, 8, 2, 3, 5, 3, 8, 8] 1 4"

(*
lemma swap_lemma1:
  assumes "i < length l"
  and "j < length l"
  shows "\<forall>k \<in> {0..<length l} - {i, j}. l!k = (swap l i j)!k"
  unfolding swap_def
  by auto

lemma swap_lemma2:
  assumes "i < length l"
  and "j < length l"
  shows "(swap l i j)!i = l!j"
  and "(swap l i j)!j = l!i" 
  unfolding swap_def
  using assms
  sledgehammer
  by (metis list_update_id nth_list_update_eq nth_list_update_neq, simp)
*)


lemma ubaci_SkoroHip1:
  assumes "SkoroHip1 l m q"
  and "q \<noteq> 0"
  and "q < m" 
  and "l ! roditelj q < l ! q"
  and "nl = swap l q (roditelj q)"
  and "m \<le> length l"
  shows "SkoroHip1 nl m (roditelj q)"
proof -
  from assms(1) have tv1: "\<forall>i \<in> {1..<m} - {q}. l!roditelj i \<ge> l!i"
    by auto

  from assms(2, 3, 5, 6) have swap1: "l!roditelj q = nl!q"
    unfolding swap_def
    by auto
  from assms(2, 3, 5, 6) have swap2: "nl!roditelj q = l!q" 
    unfolding swap_def
    by auto
  from assms(2, 3, 5, 6) have swap3: "\<forall>x . x < m \<and> x \<noteq> q \<and> x \<noteq> roditelj q \<longrightarrow> nl!x = l!x" 
    unfolding swap_def
    by auto

  from assms(1) have tv2: "najveci3roditelj l q m = roditelj q"
    by auto
  have tv3: "najveci3 nl q m = q"
  proof (cases "desno q < m")
    case True
    with tv2 have "l!roditelj q \<ge> l!levo q \<and> l!roditelj q \<ge> l!desno q"
      by (smt (verit, best) najveci3roditelj.elims)
    with swap1 swap3 True have "nl!q \<ge> nl!levo q \<and> nl!q \<ge> nl!desno q"
      by auto
    then show ?thesis
      by auto
  next
    case False
    then show ?thesis
    proof (cases "levo q < m")
      case True
      with tv2 have "l!roditelj q \<ge> l!levo q"
        by (smt (verit, best) najveci3roditelj.elims)
      with swap1 swap3 True have "nl!q \<ge> nl!levo q"
        by auto
      with False show ?thesis
        by auto
    next
      case False
      then show ?thesis
        by auto
    qed
  qed

 
  
  have "najveci3roditelj nl (roditelj q) m = roditelj (roditelj q)"
  proof (cases "2 dvd q")
    case True
    have "roditelj q < m"
      using assms(3)
      by auto
    then have "roditelj q = najveci3 l (roditelj q) m"
      using tv1
  next
    case False
    then show ?thesis sorry
  qed

   
  

  have "najveci3 l q m = q"
  proof(cases "desno q < m")
    case True

    have hL: "l!q \<ge> l!(levo q)"
    proof -
      from True assms(3) tv1 have "l!roditelj (levo q) \<ge> l!(levo q)"
        by fastforce
      then show ?thesis
         by auto
     qed    

    have hR: "l!q \<ge> l!(desno q)"
    proof -
      from True assms(3) tv1 have "l!roditelj (desno q) \<ge> l!(desno q)"
        by fastforce
      then show ?thesis
         by auto
    qed

    from hL hR show ?thesis
      by auto
  next
    case False
    show ?thesis
    proof (cases "levo q < m")
      case True
  
      have hL: "l!q \<ge> l!(levo q)"
      proof -
        from True assms(3) tv1 have "l!roditelj (levo q) \<ge> l!(levo q)"
          by fastforce
        then show ?thesis
           by auto
       qed   
      from hL False show ?thesis
        by auto
    next
      case False
      then show ?thesis
        by auto
    qed
  qed

  with assms(4, 5) swap1 swap2 have "najveci3roditelj nl q m = roditelj q"
    unfolding swap_def
    by (smt (verit, ccfv_SIG) najveci3.simps najveci3roditelj.elims nth_list_update_neq)


qed

lemma ubaci_JesteHip1:
  assumes "SkoroHip1 l m q"
  and "q < m"
  and "q = 0 \<and> l ! roditelj q \<ge> l ! q" 
  shows "JesteHip1 l m"
proof

qed

lemma ubaciSve_inv1:
assumes "i \<le> length l" (*?*)
and "JesteHip l i"
shows "JesteHip (ubaci l i) (i+1)"
  sorry

lemma ubaciSve_inv2:
assumes "i \<le> length l" (*?*)
shows "mset l = mset (ubaci l i)"
  unfolding swap_def
  sorry


lemma izbaciSve_inv1:
assumes "0 < i \<and> i \<le> length l" (*?*)
and "JesteHip l i"
and "JesteSortiran l i"
and "l ! 0 \<le> l ! i"
and "nl = (swap l 0 (i-1))"

shows "JesteHip (izbaci nl 0 (i-1)) (i-1)" 
and "JesteSortiran (izbaci nl 0 (i-1)) (i-1)"
and "nl ! 0 \<le> nl ! (i-1)"
  sorry

lemma izbaciSve_inv2:
assumes "0 < i \<and> i \<le> length l" (*?*)
shows "mset l = mset (izbaci (swap l 0 (i-1)) 0 (i-1))"
  unfolding swap_def 
  sorry


end