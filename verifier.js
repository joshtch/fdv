// NOTE: must first call the exported setSolver function with a solver
// this can be done once per entire test run (multiple files) since the closure persists

//import FDP from '../fdp/src/fdp';
//import FDO from '../fdo/src/fdo';

import {
  EMPTY,

  domain__debug,
  domain_arrToSmallest,
  domain_createValue,
  domain_divby,
  domain_intersection,
  domain_minus,
  domain_mul,
  domain_plus,
} from '../fdlib/src/domain';

let inspect = typeof require === 'function' ? function(arg) { return require('util').inspect(arg, false, null).replace(/\n ?/g, ' '); } : function(o) { return o; };

let LOG_SOLUTION = false;

let SOLVER;
function setSolver(solver) {
  console.log('FDV: setting solver now');
  // this function is exported as a closure over SOLVER and this is why it works :)
  SOLVER = solver;
}
let SCRUB_THROW_STRAT = false;
function setThrowStratMode(bool) {
  // do we automatically scrub `@custom var-strat throw` from input problems?
  // we want to do this for FDO since it won't do anything to solve without crunching
  SCRUB_THROW_STRAT = bool;
}

function max(v) {
  if (typeof v === 'number') return v;
  if (!(v instanceof Array)) throw new Error('bad value ['+v+']');
  return v[v.length-1];
}
function min(v) {
  if (typeof v === 'number') return v;
  if (!(v instanceof Array)) throw new Error('bad value ['+v+']');
  return v[0];
}
function all(v, f) {
  if (typeof v === 'number') return f(v, 0);
  if (!(v instanceof Array)) throw new Error('bad value ['+v+']');
  v.forEach(f);
}
function dom(v) {
  if (typeof v === 'number') return domain_createValue(v);
  if (!(v instanceof Array)) throw new Error('bad value ['+v+']');
  return domain_arrToSmallest(v);
}
function solved(v) {
  return typeof v === 'number';
}
function unsolved(v) {
  return typeof v !== 'number';
}
function isBooly(v) {
  return !isZero(v) && !isNonZero(v);
}
function isNonBooly(v) {
  return isZero(v) || isNonZero(v);
}
function isZero(v) {
  return max(v) === 0;
}
function isNonZero(v) {
  return min(v) > 0;
}
function parseValue(v, solution, _line, verifyOptions) {
  let va = parseInt(v, 10);
  if (va + '' === v) return va;
  if (v[0] === '[' && v[v.length-1] === ']') {
    return eval(v
      .replace(/ *, */g, ',') // remove whitespace around commas (prevents adding multiple commas)
      .replace(/ +/g, ' ')    // replace multiple spaces with one (normalize)
      .replace(/\[ +/g, '[')  // remove whitespace at start of literal
      .replace(/ +\]/g, ']')  // remove whitespace at end of literal
      .replace(/ /g,',')      // any remaining space should now be a separator of domain elements, for eval make them commas
    );
  }
  if (solution[v] === undefined) throw new Error('Value wasnt a number and it wasnt part of solution; v='+v+', v[0]='+v[0]+', line='+_line + scrubStack(verifyOptions.stack));
  return solution[v];
}

function scrubStack(stack) {
  let s = '';
    if (stack) {
      s = '\n' + stack.split(/\n/g).filter(s => s.indexOf('.spec.js') >= 0 && s.indexOf('Suite') >= 0).join('\n');
    } else {
      s = ' <no stack passed>';
    }
  return s;
}
function scrubStack2(stack) {
  let s = '';
    if (stack) {
      s = '\n' + stack.split(/\n/g).filter(s => s.indexOf('src/') >= 0).join('\n');
    } else {
      s = ' <no stack passed>';
    }
  return s;
}
function scrubToOne(stack) {
  let s = '';
    if (stack) {
      s = '\n' + stack.split(/\n/g).filter(s => s.indexOf('.spec.js') >= 0 && s.indexOf('Suite') >= 0)[0];
      s = 'line: ' + s.match(/\.js:(\d+):/)[1];
    } else {
      s = ' <no stack passed>';
    }
  return s;
}
function printSol(solution) {
  return (LOG_SOLUTION ? ', solution: ' + inspect(solution) : '');
}

function verify(dsl, ifThrowThenTheseOps='', verifyOptions, preOptions = {}, fdOptions) {
  if (!SCRUB_THROW_STRAT) {
    _verify(dsl, ifThrowThenTheseOps, verifyOptions, preOptions, fdOptions);
  }

  // many cutter tests will just throw instead of calling FD. this prevents verify from
  // actually verifying anything. so rerun the test with FD so that we can verify the result.
  // without throw var-strat, FD should solve/reject whatever remains of the problem, NEVER throw.
  // TODO: dedupe tests that (now redundantly) do this manually

  if (SCRUB_THROW_STRAT || dsl.indexOf('@custom var-strat throw') >= 0) {
    let sandsl = dsl.replace(/^\s*@custom var-strat throw\s*(?:#|$)/gm, '#');

    _verify(sandsl, ifThrowThenTheseOps === 'reject' ? 'reject' : '', verifyOptions, preOptions, fdOptions);
  }
}
function _verify(dsl, ifThrowThenTheseOps = '', verifyOptions = {}, fdpOptions = {}, fdoOptions) {
  if (typeof SOLVER !== 'function') throw new Error('Solver is not set up, set one up first');
  if (fdpOptions.hashNames === undefined) fdpOptions.hashNames = false; // prettier output, doesnt affect solving
  let solution;
  try {
    //solution = FDP.solve(dsl, FDO.solve, fdpOptions, fdoOptions);
    solution = SOLVER(dsl, fdpOptions, fdoOptions);
  } catch(e) {
    let match = e.message.match(/ops:(.*?)#/);

    if (!match) {
      // actual error unrelated to verify (hurray!), just propagate the message
      throw new Error(
        e.message +
        ', stack=' + (e.stack) + '\n===' + scrubStack(verifyOptions.stack)
      );
    }

    if (match[0] === 'ops: ' + ifThrowThenTheseOps + ' #' || ifThrowThenTheseOps === '*') {
      // ok, we expected to require FD to solve these ops
      return;
    }

    if (ifThrowThenTheseOps === 'reject') {
      throw new Error(
        'Expected problem to just reject (not throw) but got [' + match[1] + '] ' +
        scrubToOne(verifyOptions.stack)
      );
    }

    if (!ifThrowThenTheseOps) {
      throw new Error(
        'Expected to just solve but got [' + match[0] + '] ' +
        scrubToOne(verifyOptions.stack)
      );
    }

    throw new Error(
      'Expected [' + ifThrowThenTheseOps + '] got [' + match[0] + '] ' +
      scrubToOne(verifyOptions.stack));
  }

  //console.log('verifying solution...');

  if (ifThrowThenTheseOps === 'reject') {
    if (solution !== false && typeof solution !== 'string') {
      throw new Error('should reject but didnt' + scrubStack(verifyOptions.stack) + printSol(solution));
    }
  } else if (ifThrowThenTheseOps) {
    if (solution === false) {
      throw new Error('expected to throw for ops [' + ifThrowThenTheseOps + '] but it REJECTED (update ops string to \'reject\')' + scrubStack(verifyOptions.stack));
    } else {
      throw new Error('expected to throw for ops [' + ifThrowThenTheseOps + '] but it SOLVED (update test and remove the ops string)' + scrubStack(verifyOptions.stack));
    }
  } else if (solution === false || typeof solution === 'string') {
    throw new Error('should not reject but rejected (not throw!) anyways' + scrubStack(verifyOptions.stack));
  } else if (!verifyOptions.skipVerify) {
    dsl
      .split(/\n/g)
      .map(s => s.trim())
      .filter(s => !!s && s[0] !== '#' && s[0] !== '@' && s[0] !== ':')
      .forEach(s => line(s, solution, verifyOptions));
  }
}
function line(line, solution, verifyOptions) {
  //console.log('a line:', line);

  // assume this func is only used for simplified constraints. no complex compound/nesting/naming/spacing blabla
  // A @@ B
  // @@@(A B ...)
  // R = A @@ B
  // R = @@@(A B)

  // note: `/\[\s*(?:\d+(?:\s+|(?:\s*,\s*))\d+)(?:(?:\s+|(?:\s*,\s*))(?:\d+(?:\s+|(?:\s*,\s*))\d+))*\s*\]/` parses
  //       a domain literal. it kind of clutters the regexes below but meh
  // a var or solved literal is: ([\w\d_$]+)
  // combined, a "value", meaning a var, solved literal, or domain literal, is then:
  // ([\w\d_$]+|(?:\[\s*(?:\d+(?:\s+|(?:\s*,\s*))\d+)(?:(?:\s+|(?:\s*,\s*))(?:\d+(?:\s+|(?:\s*,\s*))\d+))*\s*\]))

  // R = sum(A B C)
  // R = same?(A B C)
  // without domains: /VALUE\s*=\s*([\w\d_$]+\??)\s*\((.*?)\)/
  m = line.match(/^\s*([\w\d_$]+|(?:\[\s*(?:\d+(?:\s+|(?:\s*,\s*))\d+)(?:(?:\s+|(?:\s*,\s*))(?:\d+(?:\s+|(?:\s*,\s*))\d+))*\s*\]))\s*=\s*([\w\d_$]+\??)\s*\((.*?)\)/);
  if (m) return verifyCR(m[1], m[2], m[3], solution, verifyOptions, line);

  // R = A @ B
  // without domains: /VALUE\s*=\s*VALUE\s*([^\w\d\s_\(\[\$#]+?)\s*VALUE/
  m = line.match(/^\s*([\w\d_$]+|(?:\[\s*(?:\d+(?:\s+|(?:\s*,\s*))\d+)(?:(?:\s+|(?:\s*,\s*))(?:\d+(?:\s+|(?:\s*,\s*))\d+))*\s*\]))\s*=\s*([\w\d_$]+|(?:\[\s*(?:\d+(?:\s+|(?:\s*,\s*))\d+)(?:(?:\s+|(?:\s*,\s*))(?:\d+(?:\s+|(?:\s*,\s*))\d+))*\s*\]))\s*([^\w\d\s_\(\[\$#]+?)\s*([\w\d_$]+|(?:\[\s*(?:\d+(?:\s+|(?:\s*,\s*))\d+)(?:(?:\s+|(?:\s*,\s*))(?:\d+(?:\s+|(?:\s*,\s*))\d+))*\s*\]))/);
  if (m) return verifyABR(m[1], m[2], m[3], m[4], solution, verifyOptions, line);

  // (this one after the R=A+B and R=sum(A B) to catch `A=1` cases)
  // A @ B
  // basically: /VALUE\s*([^\w\s\(\[#]+?)\s*VALUE(?:$|[^(])/
  let m = line.match(/^\s*([\w\d_$]+|(?:\[\s*(?:\d+(?:\s+|(?:\s*,\s*))\d+)(?:(?:\s+|(?:\s*,\s*))(?:\d+(?:\s+|(?:\s*,\s*))\d+))*\s*\]))\s*([^\w\s\(\[#]+?)\s*([\w\d_$]+|(?:\[\s*(?:\d+(?:\s+|(?:\s*,\s*))\d+)(?:(?:\s+|(?:\s*,\s*))(?:\d+(?:\s+|(?:\s*,\s*))\d+))*\s*\]))(?:$|[^(])/);
  if (m) return verifyAB(m[1], m[2], m[3], solution, verifyOptions, line);

  // diff(A B C)
  // without domains: /VALUE\s*\((.*?)\)/
  m = line.match(/^\s*([\w\d_$]+|(?:\[\s*(?:\d+(?:\s+|(?:\s*,\s*))\d+)(?:(?:\s+|(?:\s*,\s*))(?:\d+(?:\s+|(?:\s*,\s*))\d+))*\s*\]))\s*\((.*?)\)/);
  if (m) return verifyC(m[1], m[2], solution, verifyOptions, line);

  throw new Error('implement me too! [' + line + ']' + scrubStack(verifyOptions.stack));
}
function verifyAB(A, op, B, solution, verifyOptions, _line) {
  console.log('verifyAB:', inspect([A, op, B, printSol(solution)]).replace(/\n/g, '').replace(/ +/g, ' '));
  let a = parseValue(A, solution, _line, verifyOptions);
  let b = parseValue(B, solution, _line, verifyOptions);

  let pass = _verifyAB(a, op, b);
  if (pass === 'implement') new Error('verifyAB; implement [' + op + '][' + _line + ']');
  if (!pass) new Error(`verifyAB fail; ${a} ${op} ${b}; ${domain__debug(dom(a))} ${op} [${domain__debug(dom(b))};` + scrubStack(verifyOptions.stack) + printSol(solution));
}
function _verifyAB(a, op, b) {
  switch (op) {
    case '=':
    case '==':
      return (solved(a) && solved(b) && a === b)
    case '!=':
      return (!domain_intersection(dom(a), dom(b)))
    case '<':
      return (max(a) < min(b))
    case '<=':
      return (max(a) <= min(b))
    case '>':
      return (min(a) > max(b))
    case '>=':
      return (min(a) >= max(b))
    case '&':
      return ((min(a) !== 0) && (min(b) !== 0))
    case '^':
      return ((min(a) === 0) != (min(b) === 0))
    case '|':
      return ((min(a) !== 0) || (min(b) !== 0))
    case '!&':
      return ((min(a) === 0) || (min(b) === 0))
    case '!^':
      return ((min(a) === 0) === (min(b) === 0))
    case '!|':
      return ((min(a) === 0) === (min(b) === 0))
    case '->':
      return ((min(a) === 0) || (min(b) !== 0))
    case '!->':
      return ((min(a) !== 0) || (min(b) === 0))
    default:
      return 'implement';
  }
}
function verifyABR(R, A, op, B, solution, verifyOptions, _line) {
  console.log('verifyABR:', inspect([R,'=',A, op, B, '=>', printSol(solution), 'line:', _line]).replace(/\n/g, '').replace(/ +/g, ' '));
  let a = parseValue(A, solution, _line, verifyOptions);
  let b = parseValue(B, solution, _line, verifyOptions);
  let r = parseValue(R, solution, _line, verifyOptions);

  let lo = min(r)
  let hi = max(r)

  // R must be either 0 or have no 0. doesnt need to be solved.
  if (!(lo > 0 || hi === 0)) throw new Error('verifyABR; ' + op + ' fail; R not solved, R=' + r + ', args=' + inspect(a) + ', ' + inspect(b) + scrubStack(verifyOptions.stack) + printSol(solution));
  if (lo === hi && typeof r !== 'number') throw new Error(op + ' fail; R was solved but an array (' + (typeof r) + '), R=' + r + ', args=' + inspect(a) + ', ' + inspect(b) + scrubStack(verifyOptions.stack) + printSol(solution));

  let pass = _verifyABR(r, a, op, b);
  if (pass === 'implement') throw new Error('verifyABR; implement me pleaaaase: [' + op + '][' + _line + '] ' + [R, A, op, B, solution]);
  if (!pass) throw new Error(`verifyABR fail; ${r} = ${a} ${op} ${b}; ${domain__debug(dom(r))} = ${domain__debug(dom(a))} ${op} [${domain__debug(dom(b))}]` + scrubStack(verifyOptions.stack) + printSol(solution));
}
function _verifyABR(r, a, op, b) {
  switch (op) {
    case '==?':
      return ((min(r) > 0) === (solved(a) && solved(b) && a === b))
    case '!=?':
      return ((min(r) > 0) === !domain_intersection(dom(a), dom(b)))
    case '&?':
      return ((min(r) > 0) === (min(a) > 0 && min(b) > 0))
    case '!&?':
      return ((min(r) > 0) !== (min(a) > 0 && min(b) > 0))
    case '|?':
      return ((min(r) > 0) === (min(a) > 0 || min(b) > 0))
    case '!|?':
      return ((min(r) > 0) !== (min(a) > 0 || min(b) > 0))
    case '<?':
      return ((min(r) > 0) === (max(a) < min(b)))
    case '<=?':
      return ((min(r) > 0) === (max(a) <= min(b)))
    case '>?':
      return ((min(r) > 0) === (max(a) > min(b)))
    case '>=?':
      return ((min(r) > 0) === (max(a) >= min(b)))
    case '+':
      return solved(r) && (dom(r) === (domain_plus(dom(a), dom(b))))
    case '-':
      return solved(r) && (dom(r) === (domain_minus(dom(a), dom(b))))
    case '*':
      return solved(r) && (dom(r) === (domain_mul(dom(a), dom(b))))
    case '/':
      return solved(r) && (dom(r) === (domain_divby(dom(a), dom(b))))

    default:
      return 'implement';
  }
}
function verifyCR(R, op, args, solution, verifyOptions, _line) {
  console.log('verifyCR:', inspect([R, op, args, printSol(solution)]).replace(/\n/g, '').replace(/ +/g, ' '));

  if (args.indexOf('[') >= 0) throw new Error('dont use domain literals in a list (or fix me to support that ^^)');
  let vars = args.trim().split(/[ ,]+/g).map(v => parseValue(v, solution, _line, verifyOptions));
  if (vars.some(v => v === undefined)) throw new Error(op + ' fail; some args were undefined... ' + [args.trim().split(/[ ,]+/g), vars.join(', ')])

  let r = parseValue(R, solution, _line, verifyOptions);
  let lo = min(r)
  let hi = max(r)

  // R must be either 0 or have no 0. doesnt need to be solved.
  if (isBooly(r)) throw new Error(op + ' fail; R not booly solved (' + lo + ', ' + hi + '), R=' + r + ', args=' + inspect(vars) + scrubStack(verifyOptions.stack) + printSol(solution));
  if (lo === hi && typeof r !== 'number') throw new Error(op + ' fail; R was solved but an array (' + (typeof r) + '), R=' + r + ', args=' + inspect(vars) + scrubStack(verifyOptions.stack) + printSol(solution));

  if (op === 'sum' || op === 'div' || op === 'product' || op === 'minus') {
    if (unsolved(r)) throw new Error('verifyCR; ' + op + ' fail; R not solved, R=' + r + ', args=' + inspect(vars) + scrubStack(verifyOptions.stack) + printSol(solution));
    if (vars.some(unsolved)) {
      // note: if one product arg is zero then the others dont need to be solved (since the result is always zero)
      if (op !== 'product' || !vars.some(isZero)) throw new Error(op + ' fail; not all args were _solved_, R=' + r + ', args=' + inspect(vars) + scrubStack(verifyOptions.stack) + printSol(solution));
    }
  }

  let pass = _verifyCR(op, vars, lo);
  if (pass === 'implement') throw new Error('verifyCR; implement me pleaaaase: ' + op + '; [' + _line + ']');
  if (!pass) {
    let s = '';
    let x;
    if (op === 'sum') s = ` = ${[x=vars.reduce((a, b) => a + b),x===lo]} `;
    if (op === 'product') s = ` = ${vars.some(isZero) ? 0 : [x=vars.reduce((a, b) => a * b),x===lo]} `;
    if (op === 'minus') s = ` = ${[x=vars.reduce((a, b) => a - b),x===lo]} `;
    if (op === 'div') s = ` = ${[x=vars.reduce((a, b) => a / b),x===lo]} `;
    throw new Error(op + ' fail, R=' + r +' ('+lo+', '+hi+'), args=' + inspect(vars) + s + scrubStack(verifyOptions.stack) + printSol(solution));
  }
}
function _verifyCR(op, vars, lo) {
  let resultPassed = lo > 0;
  switch (op) {
    case 'all?':
      return resultPassed === !vars.some(isZero);

    case 'diff?': {
      let doms = vars.map(dom);
      return resultPassed === !doms.some((d,i) => {
        for (let j=i+1; j<vars.length; ++j) {
          if (domain_intersection(d, doms[j]) !== EMPTY) return true;
        }
      });
    }

    case 'nall?':
      return resultPassed === vars.some(isZero);

    case 'none?':
      return resultPassed === !vars.some(isNonZero);

    case 'same?':
      return (resultPassed === !vars.some(v => unsolved(v) || v !== vars[0]))

    case 'some?':
      return resultPassed === vars.some(isNonZero);

    case 'sum':
      return (lo === vars.reduce((a, b) => a + b))

    case 'product':
      return vars.some(isZero) ? lo === 0 : (lo === vars.reduce((a, b) => a * b))

    case 'minus':
      return (lo === vars.reduce((a, b) => a - b))

    case 'div':
      return (lo === vars.reduce((a, b) => a / b))

    default:
      return 'implement';
  }
}
function verifyC(op, args, solution, verifyOptions, _line) {
  console.log('verifyC:', inspect([op, args, printSol(solution)]).replace(/\n/g, '').replace(/ +/g, ' '));

  if (args.indexOf('[') >= 0) throw new Error('dont use domain literals in a list (or fix me to support that ^^)');
  let vars = args.trim().split(/[ ,]+/g).map(v => parseValue(v, solution, _line, verifyOptions));

  if (vars.some(v => typeof v !== 'number' && !(v instanceof Array))) throw new Error('verifyC; weird vars: ' + inspect(vars) + ' [' + op + '][' + _line + ']');

  let pass = _verifyC(op, vars);
  if (pass === 'verify') throw new Error('verifyC; implement me pleaaaase: [' + op + '][' + _line + ']');
  if (!pass) throw new Error(op + ' fail, args=' + inspect(vars) + scrubStack(verifyOptions.stack) + printSol(solution));
}
function _verifyC(op, vars) {
  switch (op) {
    case 'all':
      return (!vars.some(isZero) && !vars.some(isBooly))

    case 'diff':
      let doms = vars.map(dom);
      return (!doms.some((d,i) => {
        for (let j=i+1; j<vars.length; ++j) {
          if (domain_intersection(d, doms[j]) !== EMPTY) return true;
        }
      }))

    case 'nall':
      return (vars.some(isZero))

    case 'none':
      return (!vars.some(isNonZero) && !vars.some(isBooly))

    case 'same':
      return (vars.reduce((a, b) => a === false ? false : isNonBooly(a) && a === b && b) !== false)

    case 'some':
      return vars.some(isNonZero)

    case 'xnor':
      // all args must not be booly, then all args must be zero or nonzero but not mixed
      return (!vars.some(isBooly) && vars.some(isZero) !== vars.some(isNonZero))

    default:
      return 'implement';
  }
}

export {
  setSolver,
  setThrowStratMode,
  verify,
  _verify,
};
