// Tiny stack VM: a from-scratch implementation of make.fun's tiny stack ISA
// (kit: program/generator/subject/ISA.md). Node 22, stdlib only, deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode byte -> imm*100 + pops*10 + pushes (PUSH8 = 101, DUP = 12);
// an absent byte is an unknown opcode. From the ISA's opcode table.
const META = {
  0: 0, 1: 101, 2: 401, 3: 10, 4: 12, 5: 22, 6: 23, 7: 33,
  16: 21, 17: 21, 18: 21, 19: 21, 20: 21, 21: 21, 22: 21, 23: 11,
  24: 21, 25: 21, 26: 21, 27: 11, 28: 21, 29: 21, 30: 21, 32: 21,
  33: 21, 34: 21, 48: 200, 49: 210, 50: 210, 51: 200, 52: 0,
  64: 11, 65: 20, 80: 10, 81: 10, 82: 1, 83: 10,
};

// Runs one program on its input bytes; returns what it wrote and its exit
// code (0 HALT, v & 255 EXIT, or trap 2..11). A trap keeps prior output.
function runOne(prog: Uint8Array, input: Uint8Array) {
  const data = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  const text = new TextEncoder();
  const n = prog.length;
  let sp = 0, cp = 0, ip = 0, pc = 0, steps = 0, len = 0;
  const done = (code: number) => ({ out: out.slice(0, len), code });

  for (;;) {
    // ISA step order: step limit, pc in range, known opcode, immediate fits,
    // stack needs, then the instruction's own traps and effect.
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    const m = META[op];
    if (m === undefined) return done(5);
    const imm = (m / 100) | 0, pops = ((m / 10) | 0) % 10, pushes = m % 10;
    if (pc + imm >= n) return done(9);
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return done(2);
    if (sp - pops + pushes > 256) return done(3);
    pc = next;

    switch (op) {
      case 0: return done(0);
      case 1: data[sp++] = (prog[next - 1] << 24) >> 24; break;
      case 2:
        data[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 3: sp--; break;
      case 4: data[sp] = data[sp - 1]; sp++; break;
      case 5: { const t = data[sp - 1]; data[sp - 1] = data[sp - 2]; data[sp - 2] = t; break; }
      case 6: data[sp] = data[sp - 2]; sp++; break;
      case 7: { const a = data[sp - 3]; data[sp - 3] = data[sp - 2]; data[sp - 2] = data[sp - 1]; data[sp - 1] = a; break; }
      case 23: data[sp - 1] = (-data[sp - 1]) | 0; break;
      case 27: data[sp - 1] = ~data[sp - 1]; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        // Two-operand ops; the top is b, below it a.
        const b = data[sp - 1], a = data[sp - 2];
        let r = 0;
        switch (op) {
          case 16: r = (a + b) | 0; break;
          case 17: r = (a - b) | 0; break;
          case 18: r = Math.imul(a, b); break;
          case 19:
            if (b === 0) return done(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 20:
            if (b === 0) return done(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 21:
            if (b === 0) return done(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 22:
            if (b === 0) return done(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << (b & 31); break;
          case 29: r = a >> (b & 31); break;
          case 30: r = (a >>> (b & 31)) | 0; break;
          case 32: r = a === b ? 1 : 0; break;
          case 33: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break;
        }
        sp -= 2;
        data[sp++] = r;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = op === 48;
        if (op !== 48) {
          const v = data[--sp];
          take = op === 49 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 51:
        if (cp === 64) return done(7);
        calls[cp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 52:
        if (cp === 0) return done(8);
        pc = calls[--cp];
        break;
      case 64: {
        const addr = data[sp - 1];
        if (addr < 0 || addr >= 256) return done(6);
        data[sp - 1] = mem[addr];
        break;
      }
      case 65: {
        const addr = data[sp - 1], v = data[sp - 2];
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        mem[addr] = v;
        break;
      }
      case 80: {
        const bytes = text.encode(String(data[sp - 1]));
        if (len + bytes.length > 65536) return done(11);
        sp--;
        out.set(bytes, len);
        len += bytes.length;
        break;
      }
      case 81:
        if (len + 1 > 65536) return done(11);
        out[len++] = data[--sp] & 255;
        break;
      case 82:
        data[sp++] = ip < input.length ? input[ip++] : -1;
        break;
      case 83: return done(data[--sp] & 255);
    }
  }
}

// Driver: one run answers every instance in the input directory.
const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(IN_DIR).sort()) {
  const dir = join(IN_DIR, id);
  const outDir = join(OUT_DIR, id);
  mkdirSync(outDir, { recursive: true });
  try {
    const prog = readFileSync(join(dir, 'program.bin'));
    let input = new Uint8Array(0);
    try { input = readFileSync(join(dir, 'input.bin')); } catch { /* empty input */ }
    const { out, code } = runOne(prog, input);
    writeFileSync(join(outDir, 'stdout.bin'), out);
    writeFileSync(join(outDir, 'exit.txt'), `${code}\n`);
  } catch {
    writeFileSync(join(outDir, 'stdout.bin'), new Uint8Array(0));
    writeFileSync(join(outDir, 'exit.txt'), '0\n');
  }
}
