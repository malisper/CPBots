#!/usr/local/bin/sbcl --script

(let ((quicklisp-init (merge-pathnames "/home/michael/quicklisp/setup.lisp"
                                       (user-homedir-pathname))))
  (when (probe-file quicklisp-init)
    (load quicklisp-init)))

(ql:quickload '(:private) :silent t)

(in-package :>)
(syntax:use-syntax :clamp)

(= *random-state* (make-random-state t))

(def shuffle (cards)
  "Shuffles a list of cards."
  (if (no cards)
      '()
      (let next (rand-elt cards)
        (cons next (shuffle (rem next cards :count 1))))))

(def play ()
  (withs (moves (shuffle (append (n-of 3 1) (n-of 5 2) (n-of 5 3)))
          num (parse-integer (read-line)))
    (read-line)
    (repeat (- num 1)
      (read-line)
      (read-line))
    (prf "~{~A~^ ~}~%" (n-of 5 (pop moves)))
    (repeat 8
      ;; 2 times for each player * 2 players
      (repeat 5
        (read-line))
      (prn (pop moves)))
    (sleep 1)))

(play)
