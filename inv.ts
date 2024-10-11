const { min, max } = Math; 
type eint = number;
type eint2 = {l: eint, h: eint};

function isBottom({l, h}: eint2): boolean {
    return h < l;
}

function le(iv1: eint2, iv2: eint2): boolean {
    const {l: l1, h: h1} = iv1;
    const {l: l2, h: h2} = iv2;
    if (isBottom(iv1)) {
        return true;
    }
    if (isBottom(iv2)) {
        return false;
    }
    return l2 <= l1 && h1 <= h2;
}

function sup(iv1: eint2, iv2: eint2): eint2 {
    const {l: l1, h: h1} = iv1;
    const {l: l2, h: h2} = iv2;
    if (isBottom(iv1)) {
        return iv2;
    }
    if (isBottom(iv2)) {
        return iv1;
    }
    return {l: min(l1, l2), h: max(h1, h2)};
}

function inf(iv1: eint2, iv2: eint2): eint2 {
    const {l: l1, h: h1} = iv1;
    const {l: l2, h: h2} = iv2;
    return {l: max(l1, l2), h: min(h1, h2)};
}

const Top: eint2 = {l: -Infinity, h: Infinity};
const Bottom: eint2 = {l: Infinity, h: -Infinity};


const i1: eint2 = {l: 2, h: 5};
const i2: eint2 = {l: 1, h: 3};

console.log(`inf`, inf(i1, i2));
console.log(`sup`, sup(i1, i2));


const i3: eint2 = {l: 1, h: 2};
const i4: eint2 = {l: 4, h: 5};

console.log(`inf is bottom`, isBottom(inf(i3, i4)));
console.log(`sup`, sup(i3, i4));

function plus(iv1: eint2, iv2: eint2): eint2 {
    const {l: l1, h: h1} = iv1;
    const {l: l2, h: h2} = iv2;
    if (isBottom(iv1) || isBottom(iv2)) {
        return Bottom;
    }
    return {l: l1 + l2, h: h1+h2};
}

function neg({l, h}: eint2): eint2 {
    return {l: -l, h: -h};
}

function minus(iv1: eint2, iv2: eint2): eint2 {
    return plus(iv1, neg(iv2));
}

const isum = plus(i1, i2);
console.log(`plus`, isum);

function inv_plus(iv: eint2, iv1: eint2, iv2: eint2): [eint2, eint2] {
    return [
        sup(iv1, minus(iv, iv2)),
        sup(iv2, minus(iv, iv1)),
    ];
}

console.log(`inv_plus`, inv_plus(isum, i1, i2));

function above(iv: eint2): eint2 {
    return isBottom(iv) ? Bottom : {l: iv.l, h: Infinity};
}

function below(iv: eint2): eint2 {
    return isBottom(iv) ? Bottom : {l: -Infinity, h: iv.h};
}

function inv_less(res: boolean, iv1: eint2, iv2: eint2): [eint2, eint2] {
    return res ?
        [
            sup(iv1, below(minus(iv2, {l:1, h:1}))),
            sup(iv2, above(plus(iv1, {l:1, h:1}))),
        ]
        :
        [
            sup(iv1, above(iv2)),
            sup(iv2, below(iv1)),
        ]
}

console.log(`inv_less true`, inv_less(true, i1, i2));
console.log(`inv_less false`, inv_less(false, i1, i2));