USING: arrays assocs classes classes.algebra combinators kernel
kernel.private math math.order math.private mm9 ! mm9.single
namespaces quotations sequences words ;
IN: mm9.math

PREDICATE: multi-math-class < class
    dup null bootstrap-word eq? [
        drop f
    ] [
        number bootstrap-word class<=
    ] if ;

<PRIVATE

: bootstrap-words ( classes -- classes' )
    [ bootstrap-word ] map ;

: math-precedence ( class -- pair )
    [
        { fixnum integer rational real number object } bootstrap-words
        swap [ swap class<= ] curry find drop -1 or
    ] [
        { fixnum bignum ratio float complex object } bootstrap-words
        swap [ class<= ] curry find drop -1 or
    ] bi 2array ;

: (math-upgrade) ( max class -- quot )
    dupd = [ drop [ ] ] [ "coercer" word-prop [ ] or ] if ;

PRIVATE>

: math-class-max ( class1 class2 -- class )
    [ [ math-precedence ] bi@ after? ] most ;

: math-upgrade ( class1 class2 -- quot )
    [ math-class-max ] 2keep [ (math-upgrade) ] bi-curry@ bi
    [ dup empty? [ [ dip ] curry ] unless ] dip [ ] append-as ;

ERROR: no-multi-math-method left right generic ;

: default-multi-math-method ( generic -- quot )
    [ no-multi-math-method ] curry [ ] like ;

<PRIVATE

: (math-method) ( generic class -- quot )
    over ?lookup-method
    [ 1quotation ]
    [ default-multi-math-method ] ?if ;

PRIVATE>

: object-method ( generic -- quot )
    object bootstrap-word (math-method) ;

: multi-math-method ( word class1 class2 -- quot )
    2dup and [
        [ 2array [ declare ] curry nip ]
        [ math-upgrade nip ]
        [ math-class-max over nearest-class (math-method) ]
        3tri 3append
    ] [
        2drop object-method
    ] if ;

<PRIVATE

: make-math-method-table ( classes quot: ( ... class -- ... quot ) -- alist )
    [ bootstrap-words ] dip [ keep swap ] curry { } map>assoc ; inline

: math-alist>quot ( alist -- quot )
    [ generic-word get object-method ] dip alist>quot ;

: tag-dispatch-entry ( tag picker -- quot )
    [ "type" word-prop 1quotation [ tag ] [ eq? ] surround ] dip prepend ;

: tag-dispatch ( picker alist -- alist' )
    swap [ [ tag-dispatch-entry ] curry dip ] curry assoc-map math-alist>quot ;

: tuple-dispatch-entry ( class picker -- quot )
    [ 1quotation [ { tuple } declare class-of ] [ eq? ] surround ] dip prepend ;

: tuple-dispatch ( picker alist -- alist' )
    swap [ [ tuple-dispatch-entry ] curry dip ] curry assoc-map math-alist>quot ;

: math-dispatch-step ( picker quot: ( ... class -- ... quot ) -- quot )
    [ { bignum float fixnum } swap make-math-method-table ]
    [ { ratio complex } swap make-math-method-table tuple-dispatch ] 2bi
    tuple swap 2array prefix tag-dispatch ; inline

: fixnum-optimization ( word quot -- word quot' )
    [ dup fixnum bootstrap-word dup multi-math-method ]
    [
        ! remove redundant fixnum check since we know
        ! both can't be fixnums in this branch
        dup length 3 - cut unclip
        [ length 2 - ] [ nth ] bi prefix append
    ] bi*
    [ if ] 2curry [ 2dup both-fixnums? ] prepend ;

PRIVATE>


M: math-dispatch make-single-default-method
    drop default-multi-math-method ;

M: math-dispatch perform-dispatch
    drop dup generic-word [
        dup [ over ] [
            dup multi-math-class? [
                [ dup ] [ multi-math-method ] 2with math-dispatch-step
            ] [
                drop object-method
            ] if
        ] with math-dispatch-step
        fixnum-optimization
        define
    ] with-variable ;

PREDICATE: math-generic < multi-generic
    "dispatch-type" word-prop math-dispatch? ;


