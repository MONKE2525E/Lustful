import assert from 'node:assert/strict';
import { test } from 'node:test';
import { decodeCString, parseExecLine, parseExecTrace } from './json-production-trace.mjs';

test('interleaved exec records require a matched complete result per process', () => {
  const a = '12 execve("/a", ["/a"], 0x1 /* 1 var */ <unfinished ...>';
  const b = '13 execve("/b", ["/b"], 0x1 /* 1 var */ <unfinished ...>';
  const doneA = '12 <... execve resumed>) = 0';
  const doneB = '13 <... execve resumed>) = -1 ENOENT (No such file or directory)';
  assert.deepEqual(parseExecTrace([a, b, doneB, doneA].join('\n')).map(x => [x.executable, x.succeeded]), [['/b', false], ['/a', true]]);
  for (const trace of [a, doneA, [a, a, doneA].join('\n'), [a, doneB].join('\n'), [a, '12 <... execveat resumed>) = 0'].join('\n')]) assert.throws(() => parseExecTrace(trace));
});

test('strace C byte escapes, UTF-8, controls and escaped delimiters', () => {
  assert.equal(decodeCString(String.raw`"/tmp/caf\303\251/\"a\\b\t\n\r\a\b\v\f"`), '/tmp/café/"a\\b\t\n\r\x07\b\v\f');
  assert.equal(decodeCString(String.raw`"\x2f\x63\x61\x66\xc3\xa9"`), '/café');
  assert.equal(decodeCString(String.raw`"\1\12\123"`), '\x01\nS');
  assert.equal(decodeCString(String.raw`"\357\273\277x"`), '\uFEFFx');
});
test('malformed, truncated, NUL and non-UTF-8 strings fail closed', () => {
  for (const token of [String.raw`"\q"`, String.raw`"\x0"`, String.raw`"\400"`, String.raw`"\377"`, String.raw`"\0"`, '"x"...', '"unterminated', '"raw\ncontrol"', '"rawé"', '"a"b"', '"end\\"'])
    assert.throws(() => decodeCString(token), undefined, token);
});
test('complete execve/execveat records retain failures and decode argv', () => {
  assert.deepEqual(parseExecLine(String.raw`123 execve("/tmp/caf\303\251", ["/tmp/caf\303\251", "a, \"b\""], 0x123 /* 2 vars */) = 0`),
    { executable: '/tmp/café', argv: ['/tmp/café', 'a, "b"'], succeeded: true, relativeToFd: false });
  assert.equal(parseExecLine('123 execveat(AT_FDCWD, "/missing", ["x"], 0x0, 0) = -1 ENOENT (No such file or directory)').succeeded, false);
  assert.equal(parseExecLine('123 execveat(3, "relative", ["x"], 0x0, 0) = 0').relativeToFd, true);
  assert.equal(parseExecLine('123 execveat(3, "/usr/bin/true", ["true"], 0x0, 0) = 0').relativeToFd, false);
  assert.equal(parseExecLine('123 socket(AF_UNIX, SOCK_STREAM, 0) = 3'), null);
  assert.deepEqual(parseExecLine(String.raw`1 execve("\x2f\x78", ["\x78"], 0x0) = 0`).argv, ['x']);
});
test('incomplete or ambiguous execution records fail closed', () => {
  for (const line of [
    '1 execve("/x", ["x", ...], 0x0) = 0',
    '1 execve("/x"..., ["x"], 0x0) = 0',
    '1 execve("/x", ["x"], 0x0 <unfinished ...>',
    '1 <... execve resumed>) = 0',
    '1 execve("/x", ["x"], 0x0) = ?',
    '1 execve("/x", ["x" "y"], 0x0) = 0',
    String.raw`1 execve("/x", ["\q"], 0x0) = 0`,
    '1 execve("/x", [], 0x0) = 0',
  ]) assert.throws(() => parseExecLine(line), undefined, line);
});
