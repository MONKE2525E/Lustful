#!/usr/bin/env node
// Run from the compiler checkout after applying the artifact-only patch.
import fs from 'node:fs';
import path from 'node:path';
import os from 'node:os';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { parseExecTrace } from './json-production-trace.mjs';

const fail = message => { throw new Error(message); };
const sha = value => crypto.createHash('sha256').update(value).digest('hex');
const read = file => fs.readFileSync(file);
const put = (file, value) => { fs.mkdirSync(path.dirname(file), { recursive: true }); fs.writeFileSync(file, value); };
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const [mode, sourceArg, savedArg] = process.argv.slice(2);
if (!['oracle', 'target'].includes(mode) || !sourceArg || !savedArg || process.argv.length !== 5)
  fail('usage: node scripts/test-json-production.mjs oracle|target VERENU_SOURCE SAVED_ORACLE_DIRECTORY');
const source = fs.realpathSync(sourceArg);
const saved = path.resolve(savedArg);
// VERENU_SOURCE is a checkout directory, never an implicitly selected home path.
const sourceFile = path.join(source, 'src-tauri/src/commands/settings/api_keys.rs');
const original = read(sourceFile);
const text = original.toString('utf8');
if (!Buffer.from(text).equals(original)) fail('production source is not UTF-8');
const start = 'pub fn parse_openai_models(body: &str) -> Result<Vec<String>, String> {';
const middle = 'pub fn parse_google_models_page(body: &str) -> Result<(Vec<String>, Option<String>), String> {';
const end = '\nfn dedupe(ids: Vec<String>) -> Vec<String> {';
for (const marker of [start, middle, end]) {
  if (text.split(marker).length !== 2) fail(`source boundary is missing or ambiguous: ${marker}`);
}
const a = text.indexOf(start), b = text.indexOf(end);
if (!(a < text.indexOf(middle) && text.indexOf(middle) < b)) fail('production function ordering drift');
const bodies = text.slice(a, b);
// Whole bounded slice, including signatures and whitespace. No regex body extraction,
// brace guessing, normalization, stubs, or algorithm substitutions.
const expectedSlice = '418fc256b72b243a68efc44cf920825468d49710fdd1fd5438e81e433d426dae';
if (sha(bodies) !== expectedSlice) fail('production slice drift: review source, then explicitly update the pin and recapture oracle');

const cases = [
  ['openai-basic', '{"data":[{"id":" x "},{"id":"x"},{"id":""},{"id":"  "},{"id":7},{},null]}'],
  ['google-basic', '{"models":[{"name":"models/gemini"}],"nextPageToken":" next "}'],
  ['google-methods', '{"models":[{"name":"models/missing"},{"name":"models/null","supportedGenerationMethods":null},{"name":"models/wrong","supportedGenerationMethods":42},{"name":"models/empty","supportedGenerationMethods":[]},{"name":"models/embed","supportedGenerationMethods":["embedContent"]},{"name":"models/good","supportedGenerationMethods":[null,"generateContent"]}]}'],
  ['google-names', '{"models":[{"name":"models/"},{"name":" models/spaced "},{"name":"models/ x "},{"name":"plain"},{"name":false},{}],"nextPageToken":"  "}'],
  ['dupes', '{"data":null,"data":[{"id":"old","id":"new"},{"id":"new"}],"models":[],"nextPageToken":"old","nextPageToken":"last"}'],
  ['unicode', '{"data":[{"id":"  雪 café 😀  "},{"id":"\\uD83D\\uDE00\\u0061"},{"id":"\\u2003wide\\u2003"}],"models":[{"name":"models/雪\\uD83D\\uDE00"}],"nextPageToken":"\\u2003頁\\u2003"}'],
  ['escaped-delimiters', '{"data":[{"id":"a\\\"}/*{\\\\b\\n"}],"models":[]}'],
];
for (const shape of ['null', 'true', '3', '"text"', '[]', '{}', '{"data":null,"models":null}', '{"data":{},"models":{}}', '{"data":"x","models":7}', '{"data":[],"models":[],"nextPageToken":3}'])
  cases.push([`shape-${cases.length}`, shape]);
// Metadata is deliberately unobserved by production; its syntax must still parse.
for (const number of ['0','-0','1.0','-0.0','1.25','1e3','1e-400','5e-324','1.7976931348623157e308','18446744073709551615','18446744073709551616','-9223372036854775809','123456789012345678901234567890','1e309','-1e309','01','1.','1e','--1'])
  cases.push([`number-${number}`, `{"data":[{"id":"ok"}],"models":[{"name":"models/ok"}],"metadata":${number}}`]);
for (const bad of ['', ' ', '{', '{"data":[}', '{"models":[],}', '{"data":[]} false', '{"data":[]}\n?', '{"data":[],"x":"\\uD800"}', '{"models":[],"x":"\\uDC00"}', '{"x":"\\uD800a"}', '{"x":"\\q"}', '{"x":"\t"}', '{\n"data": [],\n"x": [1,]\n}'])
  cases.push([`malformed-${cases.length}`, bad]);
for (const depth of [126, 127, 128, 129])
  cases.push([`depth-${depth}`, `{"data":[],"models":[],"metadata":${'['.repeat(depth)}0${']'.repeat(depth)}}`]);
const raw = value => {
  if (value.includes('"####')) fail('fixture collides with Rust raw delimiter');
  return `r####"${value}"####`;
};
const driver = '\nfn main() {\n' + cases.map(([name, body], i) =>
  `    println!("case-${i}\\t{:?}\\t{:?}", parse_openai_models(${raw(body)}), parse_google_models_page(${raw(body)}));`
).join('\n') + '\n}\n';
const program = bodies + driver;
const identity = { schema: 2, sourceSha256: sha(original), sliceSha256: sha(bodies), programSha256: sha(program), corpusSha256: sha(JSON.stringify(cases)), cases: cases.map(([name]) => name), oracleDependency: '=1.0.151', edition: '2024' };
const work = fs.mkdtempSync(path.join(os.tmpdir(), 'lust-json-production-'));
console.log(`Artifacts: ${work}`);
put(path.join(work, 'identity.json'), JSON.stringify(identity, null, 2) + '\n');
put(path.join(work, 'production-slice.rs'), bodies);
const env = { ...process.env, CARGO_NET_OFFLINE: 'true', CARGO_TARGET_DIR: path.join(work, 'cargo-target') };
delete env.RUSTFLAGS; delete env.CARGO_ENCODED_RUSTFLAGS;
function run(label, command, args, runEnv = env, cwd = work) {
  const r = spawnSync(command, args, { cwd, env: runEnv, timeout: 600000, maxBuffer: 32 * 1024 * 1024 });
  put(path.join(work, `${label}.stdout`), r.stdout ?? Buffer.alloc(0));
  put(path.join(work, `${label}.stderr`), r.stderr ?? Buffer.alloc(0));
  return r;
}
function success(r, label) {
  if (r.error || r.signal || r.status !== 0) fail(`${label} failed (${r.error ?? r.signal ?? r.status}); inspect ${work}`);
}
function tracedRun(label, command, args, runEnv) {
  const trace = path.join(work, `${label}.trace`);
  const result = run(label, 'strace', ['--kill-on-exit', '-f', '-qq', '-xx', '-s', '65535', '-e', 'trace=execve,execveat,network', '-o', trace, 'timeout', '180', command, ...args], runEnv);
  if (!fs.existsSync(trace)) fail(`missing mandatory ${label} transitive trace`);
  const audit = read(trace).toString();
  let executions;
  try { executions = parseExecTrace(audit); }
  catch (error) { fail(`undecodable execution: ${trace}: ${error.message}`); }
  if (executions.some(record => record.relativeToFd)) fail(`cannot resolve fd-relative execution: ${trace}`);
  if (!executions.length || /AF_INET6?\b/.test(audit)) fail(`forbidden or incomplete network/exec trace: ${trace}`);
  return { result, executions, trace };
}
const fileIdentity = file => ({ path: fs.realpathSync(file), sha256: sha(read(file)) });
function assertUnchanged(identity) {
  if (JSON.stringify(fileIdentity(identity.path)) !== JSON.stringify(identity)) fail(`artifact changed during run: ${identity.path}`);
}
function adapterIdentity(directory) {
  const files = [];
  function visit(relative) {
    for (const entry of fs.readdirSync(path.join(directory, relative), { withFileTypes: true }).sort((a, b) => a.name < b.name ? -1 : a.name > b.name ? 1 : 0)) {
      const name = path.join(relative, entry.name);
      if (entry.isDirectory()) visit(name);
      else if (entry.isFile()) files.push({ path: name, sha256: sha(read(path.join(directory, name))) });
      else fail(`unsupported adapter entry: ${name}`);
    }
  }
  visit('');
  if (!files.length) fail('empty path adapter');
  return { path: fs.realpathSync(directory), sha256: sha(JSON.stringify(files)), files };
}
const pkg = path.join(work, 'fixture');
put(path.join(pkg, 'src/main.rs'), program);
const packageHeader = '[package]\nname = "json-production"\nversion = "0.0.0"\nedition = "2024"\n[workspace]\n[dependencies]\n';
if (mode === 'oracle') {
  if (fs.existsSync(saved)) fail('saved oracle destination already exists; choose a new directory');
  // Require a deliberate toolchain binary, not PATH's rustup proxy. CLI Cargo
  // config and environment override inherited compiler/wrapper substitutions.
  if (!process.env.JSON_ORACLE_RUSTC || !path.isAbsolute(process.env.JSON_ORACLE_RUSTC)) fail('oracle requires absolute JSON_ORACLE_RUSTC pointing directly to independent rustc');
  const oracleCompiler = fileIdentity(process.env.JSON_ORACLE_RUSTC);
  if (path.basename(oracleCompiler.path) !== 'rustc') fail('JSON_ORACLE_RUSTC must resolve to a rustc binary, not a proxy/wrapper');
  if (process.env.LUST) {
    const target = fileIdentity(process.env.LUST);
    const core = fileIdentity(path.join(path.dirname(target.path), 'lust-core'));
    if ([target, core].some(item => item.path === oracleCompiler.path || item.sha256 === oracleCompiler.sha256)) fail('oracle compiler is the compiler under test');
  }
  const oracleEnv = { ...env, RUSTC: oracleCompiler.path, RUSTC_WRAPPER: '', RUSTC_WORKSPACE_WRAPPER: '', CARGO_BUILD_RUSTC: oracleCompiler.path, CARGO_BUILD_RUSTC_WRAPPER: '', CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER: '' };
  const compilerConfig = ['--config', `build.rustc=${JSON.stringify(oracleCompiler.path)}`, '--config', 'build.rustc-wrapper=""', '--config', 'build.rustc-workspace-wrapper=""'];
  put(path.join(pkg, 'Cargo.toml'), packageHeader + 'serde_json = "=1.0.151"\n');
  const build = tracedRun('oracle-build', 'cargo', [...compilerConfig, 'build', '--offline', '--manifest-path', path.join(pkg, 'Cargo.toml')], oracleEnv);
  let fixtureCompilations = 0;
  for (const execution of build.executions) {
    const { executable, argv, succeeded } = execution;
    if (argv.includes('--crate-name')) {
      // A wrapper carrying compiler argv is also rejected, including failed
      // attempts; only the selected compiler may receive compilation work.
      if (!path.isAbsolute(executable) || fs.realpathSync(executable) !== oracleCompiler.path || argv[0] !== oracleCompiler.path) fail(`oracle compiler substitution: ${build.trace}`);
      if (succeeded && argv[argv.indexOf('--crate-name') + 1] === 'json_production') fixtureCompilations++;
    } else if (/^(?:rustc(?:-real)?|rustup|sccache|cachepot|lust(?:-core)?)(?:\.exe)?$/.test(path.basename(executable)) &&
               (!path.isAbsolute(executable) || fs.realpathSync(executable) !== oracleCompiler.path)) fail(`oracle compiler/wrapper substitution: ${build.trace}`);
  }
  if (!fixtureCompilations) fail('oracle trace does not establish selected rustc compiled the fixture');
  success(build.result, 'offline independent Cargo oracle');
  const lock = read(path.join(pkg, 'Cargo.lock'));
  if (!/name = "serde_json"\nversion = "1\.0\.151"\nsource = "registry\+[^"\n]+"\nchecksum = "[a-f0-9]{64}"/.test(lock.toString())) fail('oracle did not resolve pinned registry serde_json');
  const r = run('oracle-run', path.join(work, 'cargo-target/debug/json-production'), [], oracleEnv);
  success(r, 'oracle execution');
  if (r.stderr.length || r.stdout.toString().trimEnd().split('\n').length !== cases.length) fail('incomplete oracle output');
  const version = run('oracle-rustc-version', oracleCompiler.path, ['-Vv'], oracleEnv); success(version, 'oracle toolchain provenance');
  assertUnchanged(oracleCompiler);
  // Publish only after the complete capture succeeds; never consume its Rust artifacts.
  for (const [name, value] of Object.entries({ 'main.rs': program, 'Cargo.toml': read(path.join(pkg, 'Cargo.toml')), 'Cargo.lock': lock, 'expected.stdout': r.stdout, 'rustc-version.txt': version.stdout, 'oracle-build.trace': read(build.trace) })) put(path.join(saved, name), value);
  put(path.join(saved, 'identity.json'), JSON.stringify({ ...identity, oracleCompiler, oracleTraceSha256: sha(read(build.trace)), outputSha256: sha(r.stdout), lockSha256: sha(lock) }, null, 2) + '\n');
  console.log(`Saved independent upstream oracle: ${saved}`);
} else {
  const recorded = JSON.parse(read(path.join(saved, 'identity.json')));
  for (const [key, value] of Object.entries(identity)) if (JSON.stringify(recorded[key]) !== JSON.stringify(value)) fail(`saved oracle identity mismatch: ${key}; recapture explicitly`);
  const expected = read(path.join(saved, 'expected.stdout'));
  if (!recorded.oracleCompiler?.path || !/^[a-f0-9]{64}$/.test(recorded.oracleCompiler.sha256 ?? '') || sha(read(path.join(saved, 'oracle-build.trace'))) !== recorded.oracleTraceSha256) fail('missing or changed independent oracle evidence; recapture explicitly');
  if (sha(expected) !== recorded.outputSha256 || sha(read(path.join(saved, 'Cargo.lock'))) !== recorded.lockSha256 || !read(path.join(saved, 'main.rs')).equals(Buffer.from(program))) fail('saved oracle artifact drift');
  if (!process.env.LUST || !path.isAbsolute(process.env.LUST)) fail('target requires absolute LUST executable path');
  const lust = fs.realpathSync(process.env.LUST);
  const launcherIdentity = fileIdentity(lust);
  const coreIdentity = fileIdentity(path.join(path.dirname(lust), 'lust-core'));
  if ([launcherIdentity, coreIdentity].some(item => item.sha256 === recorded.oracleCompiler.sha256)) fail('target compiler matches oracle compiler');
  const adapter = adapterIdentity(path.join(root, 'library/deps/serde_json'));
  // Path source differential, intentionally separate from registry admission.
  put(path.join(pkg, 'Cargo.toml'), packageHeader + `serde_json = { path = ${JSON.stringify(path.join(root, 'library/deps/serde_json'))} }\n`);
  const deny = path.join(work, 'deny');
  for (const name of ['rustc', 'rustc-real', 'rustup', 'sccache', 'cachepot']) {
    const file = path.join(deny, name);
    put(file, '#!/bin/sh\nprintf "forbidden host tool\\n" >> "$JSON_HOST_LOG"\nexit 97\n'); fs.chmodSync(file, 0o755);
  }
  const strictEnv = { ...env, PATH: `${deny}:${env.PATH}`, RUSTC: path.join(deny, 'rustc'), RUSTC_WRAPPER: '', RUSTC_WORKSPACE_WRAPPER: '', JSON_HOST_LOG: path.join(work, 'host.log'), LUST_HOST_TOOLS: '0', LUST_NO_DAEMON: '1', LUST_NO_CACHE: '1', LUST_CACHE_DIR: path.join(work, 'cache'), LUST_DAEMON_SOCKET: path.join(work, 'daemon.sock') };
  const output = path.join(work, 'production.lust');
  function traced(label, command, args) {
    const { result: r, executions, trace } = tracedRun(label, command, args, strictEnv);
    // Inspect failed exec attempts as well as successful executions, including
    // absolute paths and wrapper argv. Never downgrade missing strace to a skip.
    for (const { executable, argv } of executions) {
      for (const name of [path.basename(executable), path.basename(argv[0] ?? '')]) {
        if (/^(?:rustc(?:-real)?|rustup|sccache|cachepot)(?:\.exe)?$/.test(name)) fail(`forbidden host tool: ${trace}`);
        // Cargo only discovers the graph; compilation and host preparation stay forbidden.
        if (name === 'cargo' && !['metadata', 'locate-project'].includes(argv[1])) fail(`forbidden Cargo command: ${trace}`);
      }
    }
    if (fs.existsSync(strictEnv.JSON_HOST_LOG)) fail(`forbidden host tool: ${trace}`);
    success(r, label);
    return { result: r, executions };
  }
  const build = traced('target-build', lust, ['build', path.join(pkg, 'src/main.rs'), '--manifest-path', path.join(pkg, 'Cargo.toml'), '--bin', 'json-production', '--offline', '-o', output]);
  for (const binary of [launcherIdentity, coreIdentity]) {
    if (!build.executions.some(record => record.succeeded && path.isAbsolute(record.executable) && fs.realpathSync(record.executable) === binary.path && record.argv[1] === 'build')) fail(`required compiler binary was not observed building: ${binary.path}`);
  }
  const { result: actual } = traced('target-run', output, []);
  if (actual.stderr.length || !actual.stdout.equals(expected)) fail(`exact Result/error differential mismatch; compare target-run.stdout with ${saved}/expected.stdout`);
  assertUnchanged(launcherIdentity); assertUnchanged(coreIdentity);
  if (JSON.stringify(adapterIdentity(adapter.path)) !== JSON.stringify(adapter)) fail('path adapter changed during run');
  put(path.join(work, 'PASS.json'), JSON.stringify({ ...identity, compilerPath: lust, compilerSha256: launcherIdentity.sha256, launcher: launcherIdentity, core: coreIdentity, adapter, oracleCompiler: recorded.oracleCompiler, oracleTraceSha256: recorded.oracleTraceSha256, targetBuildTraceSha256: sha(read(path.join(work, 'target-build.trace'))), targetRunTraceSha256: sha(read(path.join(work, 'target-run.trace'))), outputSha256: sha(actual.stdout), scope: 'unchanged isolated production bodies; path-source adapter only' }, null, 2) + '\n');
  console.log('Exact production Result/error parity; mandatory target build/run exec/network audit clean.');
  console.log('Not registry admission, generic Serde, async/network discovery, or desktop verification.');
}
