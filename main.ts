// Tiny stack VM for make.fun's tiny stack ISA v1 (spec: the kit's generator/subject/ISA.md;
// reference semantics: generator/subject/vm.mjs). For every instance under /input/<id>/ this
// runs program.bin on input.bin and writes /output/<id>/stdout.bin plus /output/<id>/exit.txt.
//
// Opcode table T: one char per opcode byte b (0x00..0x53), value 48 + imm*16 + pops*4 + pushes,
// where imm is the immediate length in bytes and pops/pushes are the stack checker's counts
// ('!' decodes negative, i.e. an unknown opcode). Decoding: imm = t >> 4, pops = (t & 15) >> 2,
// pushes = t & 3.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const T = '0Aq46:;?!!!!!!!!999999959995999!999!!!!!!!!!!!!!PTTP0!!!!!!!!!!!58!!!!!!!!!!!!!!4414';

function run(p, g) {
  const n = p.length;
  const D = new Int32Array(256); // data stack, max 256 values
  const C = new Int32Array(64); // call stack, max 64 return addresses
  const M = new Int32Array(256); // memory, 256 words
  const out = new Uint8Array(65536); // output buffer, max 65,536 bytes
  let sp = 0, csp = 0, ip = 0, ol = 0, pc = 0, steps = 0;
  const end = (code) => [out.subarray(0, ol), code];
  for (;;) {
    if (steps === 1e6) return end(10); // step limit reached
    if (pc < 0 || pc >= n) return end(9); // pc outside the program (falling off the end too)
    const t = T.charCodeAt(p[pc]) - 48;
    if (!(t >= 0)) return end(5); // unknown opcode
    const imm = t >> 4;
    if (pc + imm >= n) return end(9); // immediate cut off by the program's end
    steps++;
    const nx = pc + 1 + imm;
    const pops = (t & 15) >> 2, push = t & 3;
    if (sp < pops) return end(2); // stack underflow
    if (sp - pops + push > 256) return end(3); // stack overflow
    const q = pc;
    pc = nx;
    switch (p[q]) {
      case 0x00: return end(0); // HALT
      case 0x01: D[sp++] = (p[q + 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 0x02: D[sp++] = p[q + 1] | p[q + 2] << 8 | p[q + 3] << 16 | p[q + 4] << 24; break; // PUSH32
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const v = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = v; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const v = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = v; break; } // ROT
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG, wraps
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, 16-bit signed offset
        const op = p[q];
        const rel = ((p[q + 1] | p[q + 2] << 8) << 16) >> 16;
        if (op === 0x30) { pc = nx + rel; break; } // JMP always takes
        const v = D[--sp];
        if (op === 0x31 ? v === 0 : v !== 0) pc = nx + rel;
        break;
      }
      case 0x33: // CALL, 16-bit unsigned target
        if (csp === 64) return end(7);
        C[csp++] = nx;
        pc = p[q + 1] | p[q + 2] << 8;
        break;
      case 0x34: // RET
        if (csp === 0) return end(8);
        pc = C[--csp];
        break;
      case 0x40: { const a = D[sp - 1]; if (a < 0 || a > 255) return end(6); D[sp - 1] = M[a]; break; } // LOAD
      case 0x41: { const a = D[sp - 1]; if (a < 0 || a > 255) return end(6); M[a] = D[sp - 2]; sp -= 2; break; } // STORE
      case 0x50: { // PRINT, decimal, output limit writes nothing on overflow
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        sp--;
        break;
      }
      case 0x51: // PUTC, low byte
        if (ol >= 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < g.length ? g[ip++] : -1; break; // IN, -1 after exhaustion
      case 0x53: return end(D[--sp] & 255); // EXIT, low byte
      default: { // the two-operand arithmetic and logic group
        const b = D[sp - 1], a = D[sp - 2];
        let r;
        switch (p[q]) {
          case 0x10: r = a + b | 0; break; // ADD, wraps
          case 0x11: r = a - b | 0; break; // SUB, wraps
          case 0x12: r = Math.imul(a, b); break; // MUL, low 32 bits of the exact product
          case 0x13: if (!b) return end(4); r = a / b | 0; break; // DIV, truncated; INT_MIN/-1 wraps to itself
          case 0x14: if (!b) return end(4); r = a % b | 0; break; // MOD, the sign of a; x % -1 is 0
          case 0x15: if (!b) return end(4); r = (a >>> 0) / (b >>> 0) | 0; break; // DIVU
          case 0x16: if (!b) return end(4); r = (a >>> 0) % (b >>> 0) | 0; break; // MODU
          case 0x18: r = a & b; break; // AND
          case 0x19: r = a | b; break; // OR
          case 0x1a: r = a ^ b; break; // XOR
          case 0x1c: r = a << (b & 31); break; // SHL, only the low 5 bits of b count
          case 0x1d: r = a >> (b & 31); break; // SHR, arithmetic
          case 0x1e: r = a >>> (b & 31) | 0; break; // SHRU, logical, read back signed
          case 0x20: r = +(a === b); break; // EQ
          case 0x21: r = +(a < b); break; // LT, signed
          default: r = +((a >>> 0) < (b >>> 0)); break; // LTU
        }
        sp--;
        D[sp - 1] = r;
      }
    }
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const [bytes, code] = run(readFileSync(join(IN_DIR, id, 'program.bin')), readFileSync(join(IN_DIR, id, 'input.bin')));
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), bytes);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), String(code));
}
