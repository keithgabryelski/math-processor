//code based on (stolen from):
//+ Jonas Raoni Soares Silva
//@ http://jsfromhell.com/classes/math-processor [rev. #1]

MathProcessor = function(){
    var o = this;
    o.o = {
	"+": function(a, b){ return +a + b; },
	"-": function(a, b){ return a - b; },
	"%": function(a, b){ return a % b; },
	"/": function(a, b){ return a / b; },
	"*": function(a, b) {
	    if (b == 1) {
		// handle identity case for arrays
		return a
	    }
	    return a * b;
	},
	"^": function(a, b){ return Math.pow(a, b); },
	">": function(a, b){ return a > b; },
	"<": function(a, b){ return a < b; },
	"=": function(a, b){ return a == b; },
	"~": function(a, b){ return a != b; }
    };
    o.s = { "^": 4, "*": 3, "/": 3, "%": 2, "+": 1, "-": 1, ">": 0, "<": 0, "=": 0, "~": 0, };
    o.u = {"+": 1, "-": -1};
    o.parentheses = {"(": 1, ")": -1};
    o.brackets = {"[": 1, "]": -1};
    o.braces = {"{": 1, "}": -1};
};
with({p: MathProcessor.prototype}){
    p.Node = {
	node_type: null,
	operator: null,
	left: null,
	right: null,
	argument: null
    };
    p.methods = {
	div: function(a, b){ return parseInt(a / b); },
	round: function(a, b){ return Math.round(a*Math.pow(10,b))/Math.pow(10,b); },
	'if': function(a, b, c){ if (a) {return b} else {return c} },
	fra: function(a){ return a - parseInt(a); },
	min: function(n1, n2, n3, n){ for(var r = arguments[0], a, l = (a = arguments).length; l; r = Math.min(r, a[--l])); return r; },
	max: function(n1, n2, n3, n){ for(var r = arguments[0], a, l = (a = arguments).length; l; r = Math.max(r, a[--l])); return r; },
	sum: function(n1, n2, n3, n){ for(var r = 0, a, l = (a = arguments).length; l; r += a[--l]); return r; },
	average: function(n1, n2, n3, n) {
	    for (var r = 0, a, l = (a = arguments).length; l; r += a[--l])
		;
	    return r / a.length;
	},
	wma: function() {
	    var numerator = 0
	    var demonimator = 0
	    for (var n = arguments.length; n > 0; --n) {
		numerator += (n * arguments[n-1]) + (n - 1)
		demonimator += n
	    }
	    return numerator / demonimator
	},
	ema: function(a) {
	    var e = 0
	    var ar = arguments.slice(1)
	    
	    for (var n = ar.length; n > 0; --n) {
		var p = ar[n-1]
		e = e + a * (p - e)
	    }
	    return e
	},
	isnan: function(a){ return isNaN(a);},
	isfinite: function(a){ return isFinite(a);},
        number: function(a){ return isFinite(Number(a)) ? Number(a) : 0;},
    };
    p.identifiers = {
	'infinity': Infinity,
	'nan': NaN,
	'true': true,
	'false': false
    };
    p.arrays = {
    };
    p.add_identifier = function(name, value) {
	p.identifiers[name] = value
    };
    p.add_array = function(name, value) {
	p.arrays[name] = value
    };
    p.find_identifiers = function(e) {
	var _ = this
	var expression = e.gsub(/{|}|#/, '')
	var all_identifiers = expression.match(/[a-z_]+[a-z_0-9]+/g)
	var external_identifiers = []
	all_identifiers.forEach(function(ee) {
	    if (!(ee in _.methods || ee in _.identifiers || ee in external_identifiers)) {
		external_identifiers.push(ee)
	    }
	});
	return external_identifiers
    };
    p.parse = function(e) {
	var _ = this
	var n = null
	var o = []
	var x = _.RPN(e.replace(/\s/g, "").split(""))
	var s = [x]
	while (s.length > 0) {
	    n = s.pop()
	    while (n[2]) {
		o[o.length] = n
		s[s.length] = n[3]
		n = n[2]
	    }
	}
	while ((n = o.pop()) != null) {
	    var le = n[2][0]
	    var la
	    if (typeof(le)=='object' && le.t=='array') {
		la = le.v
	    } else if (isNaN(le)) {
		la = _.func(le)
	    } else {
		la = le
	    }
	    var re = n[3][0]
	    var ra
	    if (typeof(re)=='object' && re.t=='array') {
		ra = re.v
	    } else if (isNaN(re)) {
		ra = _.func(re)
	    } else {
		ra = re
	    }
	    n[0] = _.o[n[0]](la, ra)
	}
	if (typeof(x[0])=='object' && x[0].t=='array') {
	    return x[0]
	}
	return +x[0];
    };
    p.RPN = function(e) {
	var x, r, _ = this, c = r = [, , , 0];
	if (e[0] in _.u || !e.unshift("+"))
	    for(; e[1] in _.u; e[0] = _.u[e.shift()] * _.u[e[0]] + 1 ? "+" : "-");
	(c[3] = [_.u[e.shift()], c, , 0])[1][0] = "*", (r = [, , c, 0])[2][1] = r;
	(c[2] = _.evaluate(e))[1] = c;
	(!e.length && (r = c)) || (e[0] in _.s && ((c = r)[0] = e.shift(), !e.length && _.error()));
	while(e.length){
	    if(e[0] in _.u){
		for(; e[1] in _.u; e[0] = _.u[e.shift()] * _.u[e[0]] + 1 ? "+" : "-");
		(c = c[3] = ["*", c, , 0])[2] = [-1, c, , 0];
	    }
	    (c[3] = _.evaluate(e))[1] = c;
	    e[0] in _.s && (c = _.s[e[0]] > _.s[c[0]] ?
			    ((c[3] = (x = c[3], c[2]))[1][2] = [e.shift(), c, x, 0])[2][1] = c[2]
			    : r == c ? (r = [e.shift(), , c, 0])[2][1] = r
			    : ((r[2] = (x = r[2], [e.shift(), r, ,0]))[2] = x)[1] = r[2]);
	}
	return r;
    };
    p.evaluate = function(e) {
	var i, j, l, _ = this;
	if (e.length == 0) {
	    return [e,,,0];
	}
	else if ("0123456789.".indexOf(e[0]) + 1) {
	    for (i = -1, l = e.length; ++i < l && "0123456789.".indexOf(e[i]) + 1;);
	    return [+e.splice(0,i).join(""), , , 0];
	}
	else if (e[0] == "(") {
	    for (i = 0, l = e.length, j = 1; ++i < l && (e[i] in _.parentheses && (j += _.parentheses[e[i]]), j););
	    return _.RPN(l = e.splice(0,i), l.shift(), !j && e.shift());
	}
	else {
	    if (((j = e[0].toLowerCase()) >= "a" && j <= "z") || j == "_") {
		for (i = 0; ((j = e[++i]) && (j = j.toLowerCase()) >= "a" && j <= "z") || j == "_" || (j >= 0 && j <= 9););
		if (j == "(") {
		    for (var l = e.length, j = 1; ++i < l && (e[i] in _.parentheses && (j += _.parentheses[e[i]]), j););
		    return [e.splice(0,i+1).join(""), , , 0];
		} else if (j == "[") {
		    for (var l = e.length, j = 1; ++i < l && (e[i] in _.brackets && (j += _.brackets[e[i]]), j););
		    return [e.splice(0,i+1).join(""), , , 0];
		} else {
		    var identifier = e.splice(0,i).join("")
		    if (p.identifiers[identifier] != undefined) {
			return [p.identifiers[identifier],,,0];
		    } else {
			_.error("unknown identifier: '" + identifier + "'")
		    }
		}
	    }
	}
	_.error();
    };
    p.func = function(e) {
	var n, i = 0, _ = this;
//	if (e.split == undefined) {
//	    alert('UNDEFINED')
//	    return e
//	}
	if (((e = e.split(""))[i] >= "a" && e[i] <= "z") || e[i] == "_") {
	    while ((e[++i] >= "a" && e[i] <= "z") || e[i] == "_" || (e[i] >= 0 && e[i] <= 9));
	    if (e[i] == "(") {
		!_.methods[n = e.splice(0, i).join("")] && _.error("Function \"" + n + "\" not found"), e.shift();

		var a = []
		var i = -1
		var j = 1
		while (e[++i]) {
		    if (e[i] in _.parentheses) {
			j += _.parentheses[e[i]]
			if (j == 0) {
			    break;
			}
		    }
		    if (j == 1 && e[i] == ",") {
			var arg = _.parse(e.splice(0, i).join(""))
			if (typeof(arg)=='object' && arg.t=='array') {
			    for (var t = 0; t < arg.v.length; ++t) {
				a.push(arg.v[t])
			    }
			} else {
			    a.push(arg)
			}
			e.shift()
			i = -1
		    }
		}
		if (a.length > 0 || i != 0) {
		    var arg = _.parse(e.splice(0,i).join(""))
		    if (typeof(arg)=='object' && arg.t=='array') {
			for (var t = 0; t < arg.v.length; ++t) {
			    a.push(arg.v[t])
			}
		    } else {
			a.push(arg)
		    }
		}
		if (j == 0) {
		    e.shift()
		}
		return _.methods[n].apply(_, a);
	    } else if (e[i] == "[") {
		!_.arrays[n = e.splice(0, i).join("")] && _.error("Array \"" + n + "\" not found"), e.shift();

		var a = []
		var i = -1
		var j = 1
		while (e[++i]) {
		    if (e[i] in _.brackets) {
			j += _.brackets[e[i]]
			if (j == 0) {
			    break;
			}
		    }
		    if (j == 1 && e[i] == ",") {
			var arg = _.parse(e.splice(0, i).join(""))
			if (typeof(arg)=='object' && arg.t=='array') {
			    for (var t = 0; t < arg.v.length; ++t) {
				a.push(arg.v[t])
			    }
			} else {
			    a.push(arg)
			}
			e.shift()
			i = -1
		    }
		}
		if (a.length > 0 || i != 0) {
		    var arg = _.parse(e.splice(0,i).join(""))
		    if (typeof(arg)=='object' && arg.t=='array') {
			for (var t = 0; t < arg.v.length; ++t) {
			    a.push(arg.v[t])
			}
		    } else {
			a.push(arg)
		    }
		}
		if (j == 0) {
		    e.shift()
		}
		var ar = _.arrays[n]
		if (a.length == 0) {
		    // ar[] = length of array
		    return {t: 'array', v: ar}
		} else if (a.length == 1) {
		    // n[x]
		    var arg1 = a[0]
		    if (arg1 < 0) {
			var start = Math.max(0, _.identifiers['_index'] + arg1)
			var end = _.identifiers['_index'] + 1
			return {t: 'array', v: ar.slice(start, end)}
		    }
		    return ar[arg1]
		} else if (a.length == 2) {
		    // n[x,y]
		    var arg1 = a[0]
 		    var arg2 = a[1]
		    return {t: 'array', v: ar.slice(arg1,arg2)}
		}
		_.error('invalid array access')
	    } else if (e[i] == ".") {
		// .length
	    } else {
		var identifier = e.splice(0,i+1).join("")
		if (p.identifiers[identifier] != undefined) {
		    return p.identifiers[identifier]
		} else {
		    _.error("Unknown identifier: '" + identifier + "'")
		}
	    }
	}
    };
    p.error = function(s) {
	throw new Error("MathProcessor: " + (s || "bad expression"));
    };
}
