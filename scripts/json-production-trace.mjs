// strace strings are byte-oriented C strings, not JSON strings.
import { TextDecoder } from 'node:util';

const reject = () => { throw new Error('undecodable or truncated strace execution'); };
const utf8 = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true });
export function decodeCString(token) {
  if (token[0] !== '"' || token.at(-1) !== '"') reject();
  const bytes = [];
  const escapes = { a: 7, b: 8, t: 9, n: 10, v: 11, f: 12, r: 13, '"': 34, "'": 39, '?': 63, '\\': 92 };
  for (let i = 1; i < token.length - 1; i++) {
    const c = token[i];
    if (c !== '\\') {
      // With -xx strace emits only ASCII escapes. Also accept its default
      // printable ASCII format for saved trace inspection.
      if (c === '"' || c.charCodeAt(0) < 32 || c.charCodeAt(0) > 126) reject();
      bytes.push(c.charCodeAt(0));
    } else {
      const escape = token[++i];
      if (i >= token.length - 1) reject();
      if (Object.hasOwn(escapes, escape)) bytes.push(escapes[escape]);
      else if (/[0-7]/.test(escape)) {
        let octal = escape;
        while (octal.length < 3 && /[0-7]/.test(token[i + 1] ?? '')) octal += token[++i];
        const value = Number.parseInt(octal, 8);
        if (value > 255) reject();
        bytes.push(value);
      } else if (escape === 'x') {
        const hex = token.slice(i + 1, i + 3);
        if (!/^[a-fA-F0-9]{2}$/.test(hex)) reject();
        bytes.push(Number.parseInt(hex, 16)); i += 2;
      } else reject();
    }
  }
  // An exec pathname/argument cannot contain NUL. Invalid UTF-8 cannot be
  // represented safely by Node filesystem APIs, so reject rather than replace.
  if (bytes.includes(0)) reject();
  return utf8.decode(Uint8Array.from(bytes));
}

const quoted = '"(?:\\\\.|[^"\\\\])*"';
const execution = new RegExp(`\\b(execve|execveat)\\((?:([^,]+), )?(${quoted}), (\\[(?:${quoted}(?:, )?)*\\]), `);
export function parseExecTrace(text) {
  const pending = new Map();
  const records = [];
  for (const line of text.split('\n')) {
    const resumed = line.match(/^(\d+) +<\.\.\. (execve(?:at)?) resumed>(.*)$/);
    let complete = line;
    if (resumed) {
      const entry = pending.get(resumed[1]);
      if (!entry || entry.call !== resumed[2]) reject();
      pending.delete(resumed[1]);
      complete = entry.prefix + resumed[3];
    } else if (/\bexecve(?:at)?\(/.test(line) && /<unfinished \.\.\.>$/.test(line)) {
      const start = line.match(/^(\d+) +(execve(?:at)?)\(/);
      if (!start || pending.has(start[1])) reject();
      pending.set(start[1], { call: start[2], prefix: line.replace(/<unfinished \.\.\.>$/, '') });
      continue;
    }
    const record = parseExecLine(complete);
    if (record) records.push(record);
  }
  if (pending.size) reject();
  return records;
}
export function parseExecLine(line) {
  // Split/resumed records cannot establish the complete argv and outcome.
  if (/<\.\.\. execve(?:at)? resumed>/.test(line)) reject();
  if (!/\bexecve(?:at)?\(/.test(line)) return null;
  const match = execution.exec(line);
  if (!match || (match[1] === 'execve' && match[2] !== undefined) ||
      (match[1] === 'execveat' && match[2] === undefined)) reject();
  const tail = line.slice(match.index + match[0].length);
  if (!/\)\s+= (?:0|-1 [A-Z0-9_]+(?: \([^\n]*\))?)$/.test(tail) || /<unfinished \.\.\.>/.test(line)) reject();
  const executable = decodeCString(match[3]);
  const contents = match[4].slice(1, -1);
  const tokens = contents ? contents.match(new RegExp(quoted, 'g')) : [];
  if (tokens.join(', ') !== contents) reject();
  const argv = tokens.map(decodeCString);
  if (!executable || !argv.length || !argv[0]) reject();
  return { executable, argv, succeeded: /\)\s+= 0$/.test(tail), relativeToFd: match[1] === 'execveat' && match[2] !== 'AT_FDCWD' && !executable.startsWith('/') };
}
