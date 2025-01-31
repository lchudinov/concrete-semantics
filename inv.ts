const { min, max } = Math;
type eint = number;
type eint2 = { l: eint, h: eint };

function isBottom({ l, h }: eint2): boolean {
	return h < l;
}

function le(iv1: eint2, iv2: eint2): boolean {
	const { l: l1, h: h1 } = iv1;
	const { l: l2, h: h2 } = iv2;
	if (isBottom(iv1)) {
		return true;
	}
	if (isBottom(iv2)) {
		return false;
	}
	return l2 <= l1 && h1 <= h2;
}

function sup(iv1: eint2, iv2: eint2): eint2 {
	const { l: l1, h: h1 } = iv1;
	const { l: l2, h: h2 } = iv2;
	if (isBottom(iv1)) {
		return iv2;
	}
	if (isBottom(iv2)) {
		return iv1;
	}
	return { l: min(l1, l2), h: max(h1, h2) };
}

function inf(iv1: eint2, iv2: eint2): eint2 {
	const { l: l1, h: h1 } = iv1;
	const { l: l2, h: h2 } = iv2;
	return { l: max(l1, l2), h: min(h1, h2) };
}

const Top: eint2 = { l: -Infinity, h: Infinity };
const Bottom: eint2 = { l: Infinity, h: -Infinity };


const i1: eint2 = { l: 2, h: 5 };
const i2: eint2 = { l: 1, h: 3 };

console.log(`inf`, inf(i1, i2));
console.log(`sup`, sup(i1, i2));


const i3: eint2 = { l: 1, h: 2 };
const i4: eint2 = { l: 4, h: 5 };

console.log(`inf is bottom`, isBottom(inf(i3, i4)));
console.log(`sup`, sup(i3, i4));

function plus(iv1: eint2, iv2: eint2): eint2 {
	const { l: l1, h: h1 } = iv1;
	const { l: l2, h: h2 } = iv2;
	if (isBottom(iv1) || isBottom(iv2)) {
		return Bottom;
	}
	return { l: l1 + l2, h: h1 + h2 };
}

function neg({ l, h }: eint2): eint2 {
	return { l: -l, h: -h };
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
	return isBottom(iv) ? Bottom : ({ l: iv.l, h: Infinity });
}

function below(iv: eint2): eint2 {
	return isBottom(iv) ? Bottom : { l: -Infinity, h: iv.h };
}

function inv_less(res: boolean, iv1: eint2, iv2: eint2): [eint2, eint2] {
	return res ?
		[
			sup(iv1, below(minus(iv2, { l: 1, h: 1 }))),
			sup(iv2, above(plus(iv1, { l: 1, h: 1 }))),
		]
		:
		[
			sup(iv1, above(iv2)),
			sup(iv2, below(iv1)),
		]
}

console.log(`inv_less true`, inv_less(true, i1, i2));
console.log(`inv_less false`, inv_less(false, i1, i2));

{
	let x: number;
	let y = 7; // Some{(x, [-Inf, +Inf]), (y, [7, 7])}
	if (x < y) {
		// Some{(x, [-Inf, 6]), (y, [7, 7])}
		y = y + x;
		// Some{(x, [-Inf, 6]), (y, [-Inf, 13])}
	} else {
		// Some{(x, [7, Inf]), (y, [7, 7])}
		x = x + y;
		// Some{(x, [14, Inf]), (y, [7, 7])}
	}
	// Some{(x, [-Inf, Inf]), (y, [-Inf, 13])}
}

{
	let x: number;
	// Some{(x, [-Inf, +Inf])}
	while (x < 100) {
		// Some{(x, [-Inf, 99])}
		x = x + 1;
		// Some{(x, [-Inf, 100])}
	}
	// Some{(x, [100, Inf])}
}

{
	let x: number;
	// Some{(x, [-Inf, +Inf])}
	while (x < 100) {
		// Some{(x, [-Inf, 99])}
		x = x + 1;
		// Some{(x, [-Inf, 100])}
	}
	// Some{(x, [100, Inf])}
}

{
	// after five steps we have

	let x: number = 0; // Some{(x, [0, 0])}
	// Some{(x, [0, 1])}
	while (x < 100) {
		// Some{(x, [0, 0])}
		x = x + 1;
		// Some{(x, [1, 1])}
	}
	// None
}

{
	// it takes a while to reach a least fixpoint  
	let x: number = 0; // Some{(x, [0, 0])}
	// Some{(x, [0, 100])}
	while (x < 100) {
		// Some{(x, [0, 99])}
		x = x + 1;
		// Some{(x, [1, 100])}
	}
	// Some{(x, [100, 100])}
}

/*
{
	// after 50 steps
	let x: number = 0; // Some{(x, [0, 0])}
	// Some{(x, [0, 16])}
	while (x > -1) {
		// Some{(x, [0, 15])}
		x = x + 1;
		// Some{(x, [1, 16])}
	}
	// None
}
*/

function widening({l: l1, h: h1}: eint2, {l: l2, h: h2}: eint2): eint2 {
	const l = (l1 > l2) ? -Infinity : l1;
	const h = (h1 < h2) ?  Infinity : h1;
	return {l, h};
}

{
	const a: eint2 = {l: 0, h: 1};
	const b: eint2 = {l: 0, h: 2};
	const c: eint2 = {l: 1, h: 2};
	const d: eint2 = {l: 0, h: 5};

	console.log(`widening(a,b)`, widening(a, b));
	console.log(`widening(b,a)`, widening(b, a));
	console.log(`widening(c,d)`, widening(c, d));

}

// widening and narrowing
{
	let x: number = 0; // Some{(x, [0, 0])}
	// Some{(x, [0, 0])}
	while (x >= -1) {
		// Some{(x, [0, 0])}
		x = x + 1;
		// Some{(x, [1, 1])}
	}
	// None
}

{
	// after first step with widening
	let x: number = 0; // Some{(x, [0, 0])}
	// Some{(x, [0, Infinity])}
	while (x >= -1) {
		// Some{(x, [0, 0])}
		x = x + 1;
		// Some{(x, [1, 1])}
	}
	// None
}

{
	// after two more steps we reach the pre-fixpoint
	// This is very nice because we have actually reached the least fixpoint.
	let x: number = 0; // Some{(x, [0, 0])}
	// Some{(x, [0, Infinity])}
	while (x >= -1) {
		// Some{(x, [0, Infinity])}
		x = x + 1;
		// Some{(x, [1, Infinity])}
	}
	// None
}

{
	// Now we look at the program where previously we needed O(n) steps to
	// reach the least fixpoint. Now we reach a pre-fixpoint very quickly:
	let x: number = 0; // Some{(x, [0, 0])}
	// Some{(x, [0, Infinity])}
	while (x < 100) {
		// Some{(x, [0, Infinity])}
		x = x + 1;
		// Some{(x, [1, Infinity])}
	}
	// // Some{(x, [100, Infinity])}
}