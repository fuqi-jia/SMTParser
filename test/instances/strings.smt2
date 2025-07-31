; String theory edge cases that trigger parser bugs
(set-logic QF_S)

; ========================================
; Section 1: Special String Contents
; ========================================

; Empty string
(declare-const empty String)
(assert (= empty ""))

; String with quotes
(declare-const quoted String)
(assert (= quoted """"))

; String with escape sequences  
(declare-const escaped String)
(assert (= escaped "\n\t\r\\"))

; String with unicode
(declare-const unicode String)
(assert (= unicode "café"))

; Very long string
(declare-const long_str String)
(assert (= long_str "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"))

; ========================================
; Section 2: String Operations Edge Cases
; ========================================

; String length of empty string
(assert (= (str.len empty) 0))

; Substring at boundaries
(declare-const test_str String)
(assert (= test_str "hello"))
(assert (= (str.substr test_str 0 0) ""))
(assert (= (str.substr test_str 5 0) ""))

; String contains empty string
(assert (str.contains test_str ""))

; String indexof with empty string
(assert (= (str.indexof test_str "" 0) 0))

; ========================================
; Section 3: Regular Expression Edge Cases
; ========================================

; Empty regex
(assert (str.in_re empty (str.to_re "")))

; Regex with special characters
(assert (str.in_re "." (str.to_re ".")))

; Kleene star with empty
(assert (str.in_re "" (re.* (str.to_re "a"))))

(check-sat)
(exit)