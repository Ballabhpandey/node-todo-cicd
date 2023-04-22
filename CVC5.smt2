; https://cvc5.github.io/app/
(set-logic ALL)
(set-option :produce-models true)
(define-sort LElement () (Set Int))
(declare-const E1 LElement)
(declare-const E2 LElement)
(declare-const E3 LElement)
(declare-const E4 LElement)

(define-sort LModule () (Set Int))
(declare-const M1 LElement)
(declare-const M2 LElement)
(declare-const M3 LElement)
(declare-const M4 LElement)
(declare-const M5 LElement)

(assert (= (set.inter E1 E2) (as set.empty (Set Int)))) ; Lifted Elements are disjoints
(assert (= (set.inter E1 E3) (as set.empty (Set Int))))
(assert (= (set.inter E1 E4) (as set.empty (Set Int))))
(assert (= (set.inter E2 E3) (as set.empty (Set Int))))
(assert (= (set.inter E2 E4) (as set.empty (Set Int))))
(assert (= (set.inter E3 E4) (as set.empty (Set Int))))

(assert (= (set.inter M1 M2) (as set.empty (Set Int)))) ; Lifted Modules are disjoints
(assert (= (set.inter M1 M3) (as set.empty (Set Int))))
(assert (= (set.inter M1 M4) (as set.empty (Set Int))))
(assert (= (set.inter M1 M5) (as set.empty (Set Int))))
(assert (= (set.inter M2 M3) (as set.empty (Set Int))))
(assert (= (set.inter M2 M4) (as set.empty (Set Int))))
(assert (= (set.inter M2 M5) (as set.empty (Set Int))))
(assert (= (set.inter M3 M4) (as set.empty (Set Int))))
(assert (= (set.inter M3 M5) (as set.empty (Set Int))))
(assert (= (set.inter M4 M5) (as set.empty (Set Int))))

(declare-datatypes ((ElementType 0)) (((A) (B) (C) (D))))
(declare-fun typeOfE (LElement) ElementType) ; typeOfE: LElement -> ElementType
(declare-datatypes ((ModuleType 0)) (((I) (II) (III) (IV) (V))))
(declare-fun typeOfM (LModule) ModuleType) ; typeOfM: LModule -> ModuleType


(declare-fun elementOfM (LModule) LElement) ; elementOfM: LModule -> LElement

; number of modules required per element
(define-fun countOfMET ((e LElement) (t ModuleType)) Int (+   ; countOfMET: LElement * ModuleType -> Int
 (ite (and (= e (elementOfM M1)) (= t (typeOfM M1))) (set.card M1) 0)
 (ite (and (= e (elementOfM M2)) (= t (typeOfM M2))) (set.card M2) 0)
 (ite (and (= e (elementOfM M3)) (= t (typeOfM M3))) (set.card M3) 0)
 (ite (and (= e (elementOfM M4)) (= t (typeOfM M4))) (set.card M4) 0)
 (ite (and (= e (elementOfM M5)) (= t (typeOfM M5))) (set.card M5) 0)
))
(define-fun ETC ((et ElementType) (mt ModuleType) (num Int)) Bool (and
    (=> (= et (typeOfE E1)) (= num (countOfMET E1 mt)))
    (=> (= et (typeOfE E2)) (= num (countOfMET E2 mt)))
    (=> (= et (typeOfE E3)) (= num (countOfMET E3 mt)))
    (=> (= et (typeOfE E4)) (= num (countOfMET E4 mt)))
))
(assert (ETC A I 1))
(assert (ETC B II 2))
(assert (ETC C III 3))
(assert (ETC D IV 4))


; there is 1 element of each type
(define-fun countOfET ((t ElementType)) Int (+   ; ElementType: Int -> Int
 (ite (= t (typeOfE E1)) (set.card E1) 0)
 (ite (= t (typeOfE E2)) (set.card E2) 0)
 (ite (= t (typeOfE E3)) (set.card E3) 0)
 (ite (= t (typeOfE E4)) (set.card E4) 0)
))
(assert (= (countOfET A) 1))
(assert (= (countOfET B) 1))
(assert (= (countOfET C) 1))
(assert (= (countOfET D) 1))

(check-sat)
(get-model)