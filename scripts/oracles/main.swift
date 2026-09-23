import Foundation
import PrimitiveTypes

// This file is compiled in the same module as the unmodified upstream Interpreter sources.
struct OracleHandler: InterpreterHandler {
    func beforeOpcodeExecution(machine: Machine, opcode: Opcode?) -> Machine.ExitError? { nil }
    func balance(address: H160) -> U256 { .ZERO }
    func gasPrice() -> U256 { .ZERO }
    func origin() -> H160 { H160(from: [UInt8](repeating: 0, count: 20)) }
    func chainId() -> U256 { .ZERO }
    func coinbase() -> H160 { origin() }
}

// Wire format: mode|gas|comma-separated decimal code|comma-separated hex stack (bottom first).
// mode is step or run. Only fork-independent STOP/ADD and undefined bytes are compared.
while let line = readLine() {
    let parts = line.split(separator: "|", omittingEmptySubsequences: false).map(String.init)
    precondition(parts.count == 4)
    let code = parts[2].split(separator: ",").map { UInt8($0)! }
    let zero = H160(from: [UInt8](repeating: 0, count: 20))
    let machine = Machine(data: [], code: code, gasLimit: UInt64(parts[1])!, memoryLimit: 0,
        context: Machine.Context(targetAddress: zero, callerAddress: zero, callValue: .ZERO),
        state: ExecutionState(), handler: OracleHandler(), hardFork: .Osaka)
    for word in parts[3].split(separator: ",") {
        switch machine.stack.push(value: try U256.fromString(hex: String(word)).get()) {
        case .success: break
        case .failure: fatalError("invalid oracle input stack")
        }
    }
    machine.machineStatus = .Continue
    if parts[0] == "step" { machine.step() } else { machine.evalLoop() }
    let status: String
    switch machine.machineStatus {
    case .Continue: status = "running"
    case .Exit(.Success(.Stop)): status = "stopped"
    case .Exit(.Error(.StackUnderflow)): status = "underflow"
    case .Exit(.Error(.OutOfGas)): status = "oog"
    case .Exit(.Error(.InvalidOpcode)): status = "invalid"
    default: fatalError("unexpected oracle status")
    }
    let words = machine.stack.data.map { $0.toBigEndian.map { String(format: "%02x", $0) }.joined() }
    print("\(status)|\(machine.gas.remaining)|\(machine.pc)|\(words.joined(separator: ","))")
}
