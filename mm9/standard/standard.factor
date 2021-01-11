USING: accessors arrays kernel layouts make math mm9 ! mm9.single mm9.single.private
namespaces quotations sequences words ;
QUALIFIED-WITH: generic.single.private gsp
IN: mm9.standard

M: single-standard-dispatch check-dispatch-effect
    [ single-dispatch# ] [ in>> length ] bi* over >
    [ drop ] [ bad-dispatch-position ] if ;

PREDICATE: single-standard-generic < multi-generic
    "dispatch-type" word-prop single-standard-dispatch? ;

PREDICATE: single-simple-generic < single-standard-generic
    "dispatch-type" word-prop #>> 0 = ;

CONSTANT: single-simple-dispatch
    T{ single-standard-dispatch f 0 }

: define-single-simple-generic ( word effect -- )
    [ single-simple-dispatch ] dip define-single-generic ;

M: single-standard-dispatch [picker]
    dispatch-type get #>> picker ;

M: single-standard-dispatch single-dispatch# #>> ;

M: single-standard-generic effective-method
    [ get-datastack ] dip [ "dispatch-type" word-prop #>> swap <reversed> nth ] keep
    method-for-object ;

: inline-cache-quot ( word methods miss-word -- quot )
    [ [ literalize , ] [ , ] [ dispatch-type get #>> , { } , , ] tri* ] [ ] make ;

M: single-standard-dispatch inline-cache-quots
    ! Direct calls to the generic word (not tail calls or indirect calls)
    ! will jump to the inline cache entry point instead of the megamorphic
    ! dispatch entry point.
    [ \ gsp:inline-cache-miss inline-cache-quot ]
    [ \ gsp:inline-cache-miss-tail inline-cache-quot ]
    2bi ;

: make-empty-cache ( -- array )
    mega-cache-size get f <array> ;

M: single-standard-dispatch mega-cache-quot
    dispatch-type get #>> make-empty-cache \ gsp:mega-cache-lookup [ ] 4sequence ;
