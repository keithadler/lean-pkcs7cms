// Apple Security framework: CMSDecoder, the CMS verifier behind macOS code signing and S/MIME in Mail.
// The signer's status is read without evaluating trust, so only the signature is judged.
// One JSON line per case.
import Foundation
import Security

let dir = URL(fileURLWithPath: CommandLine.arguments[1])
let manifest = try! String(contentsOf: dir.appendingPathComponent("manifest.tsv"), encoding: .utf8)
for line in manifest.split(separator: "\n") {
    let f = line.split(separator: "\t", omittingEmptySubsequences: false).map(String.init)
    let id = f[0]
    func out(_ ok: Bool, _ err: String) {
        let e = err.replacingOccurrences(of: "\"", with: "'")
        print("{\"id\":\"\(id)\",\"ok\":\(ok),\"err\":\"\(e)\"}")
    }
    let msg = try! Data(contentsOf: dir.appendingPathComponent(f[1]))
    var dec: CMSDecoder?
    guard CMSDecoderCreate(&dec) == errSecSuccess, let d = dec else { out(false, "create"); continue }
    if f[2] != "" {
        let content = try! Data(contentsOf: dir.appendingPathComponent(f[2])) as CFData
        CMSDecoderSetDetachedContent(d, content)
    }
    var st = msg.withUnsafeBytes { CMSDecoderUpdateMessage(d, $0.baseAddress!, msg.count) }
    if st != errSecSuccess { out(false, "update \(st)"); continue }
    st = CMSDecoderFinalizeMessage(d)
    if st != errSecSuccess { out(false, "finalize \(st)"); continue }
    var n = 0
    CMSDecoderGetNumSigners(d, &n)
    if n == 0 { out(false, "no signers"); continue }
    let policy = SecPolicyCreateBasicX509()
    var allOk = true
    var why = ""
    for i in 0..<n {
        var status = CMSSignerStatus.unsigned
        var certStatus: OSStatus = 0
        let r = CMSDecoderCopySignerStatus(d, i, policy, false, &status, nil, &certStatus)
        if r != errSecSuccess || status != .valid { allOk = false; why = "signer \(i): status \(status.rawValue), result \(r)" }
    }
    out(allOk, why)
}
