import { useState } from 'react';

function App() {
  const [mode, setMode] = useState('validation');
  const [code1, setCode1] = useState('arr := [1, 2, 3, 4];\nx := 0;\nwhileloop (x < 3):\n    forloop i in range(2):\n        if (arr[i] > arr[i + 1]):\n            temp := arr[i]\n            if (temp > 2):\n                arr[i] := arr[i + 1]\n            else:\n                arr[i] := temp + 1\n            arr[i + 1] := temp\n    x := x + 1');
  const [code2, setCode2] = useState('');
  const [assertion, setAssertion] = useState('(assert (> arr0_1 2))');
  const [loopBound, setLoopBound] = useState(3);
  const [result, setResult] = useState(null);
  const [error, setError] = useState(null);
  const [loading, setLoading] = useState(false);

  const handleSubmit = async () => {
    setError(null);
    setResult(null);
    setLoading(true);

    try {
      const endpoint = mode === 'validation' ? '/validate' : '/equivalence';
      const body = mode === 'validation' 
        ? { code: code1, loop_bound: loopBound, assertion }
        : { code1, code2, loop_bound: loopBound, assertion };

      const response = await fetch(endpoint, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(body)
      });

      const data = await response.json();
      
      if (response.ok) {
        setResult(data);
      } else {
        setError(data.error || 'An error occurred');
      }
    } catch (err) {
      setError('Failed to connect to the backend: ' + err.message);
    } finally {
      setLoading(false);
    }
  };

  return (
    <div className="min-h-screen bg-gray-50 py-8 px-4">
      <div className="max-w-4xl mx-auto">
        <h1 className="text-3xl font-bold text-center mb-8">SMT Validator</h1>
        
        <div className="bg-white rounded-lg shadow-md p-6 mb-6">
          <div className="flex gap-4 mb-6">
            <button
              onClick={() => setMode('validation')}
              className={`flex-1 py-2 px-4 rounded-md transition-colors ${
                mode === 'validation'
                  ? 'bg-blue-600 text-white'
                  : 'bg-gray-200 hover:bg-gray-300'
              }`}
            >
              SMT Validation
            </button>
            <button
              onClick={() => setMode('equivalence')}
              className={`flex-1 py-2 px-4 rounded-md transition-colors ${
                mode === 'equivalence'
                  ? 'bg-blue-600 text-white'
                  : 'bg-gray-200 hover:bg-gray-300'
              }`}
            >
              Equivalence Checking
            </button>
          </div>

          <div className="space-y-4">
            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Program Code {mode === 'equivalence' && '(First Program)'}
              </label>
              <textarea
                value={code1}
                onChange={(e) => setCode1(e.target.value)}
                className="w-full h-48 p-3 border rounded-md font-mono text-sm"
                placeholder="Enter your code here..."
              />
            </div>

            {mode === 'equivalence' && (
              <div>
                <label className="block text-sm font-medium text-gray-700 mb-1">
                  Second Program Code
                </label>
                <textarea
                  value={code2}
                  onChange={(e) => setCode2(e.target.value)}
                  className="w-full h-48 p-3 border rounded-md font-mono text-sm"
                  placeholder="Enter the second program code here..."
                />
              </div>
            )}

            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                SMT Assertion
              </label>
              <textarea
                value={assertion}
                onChange={(e) => setAssertion(e.target.value)}
                className="w-full h-24 p-3 border rounded-md font-mono text-sm"
                placeholder="(assert (> arr0_1 2))"
              />
            </div>

            <div>
              <label className="block text-sm font-medium text-gray-700 mb-1">
                Loop Unrolling Bound (1-5)
              </label>
              <input
                type="number"
                value={loopBound}
                onChange={(e) => setLoopBound(Number(e.target.value))}
                min="1"
                max="5"
                className="w-full p-3 border rounded-md"
              />
            </div>

            <button
              onClick={handleSubmit}
              disabled={loading}
              className="w-full py-3 bg-blue-600 text-white rounded-md hover:bg-blue-700 disabled:bg-gray-400 disabled:cursor-not-allowed transition-colors"
            >
              {loading ? 'Processing...' : 'Run Analysis'}
            </button>
          </div>
        </div>

        {error && (
          <div className="bg-red-50 border border-red-200 text-red-700 p-4 rounded-md mb-6">
            {error}
          </div>
        )}

        {result && (
          <div className="bg-white rounded-lg shadow-md p-6 space-y-6">
            {mode === 'validation' ? (
              <>
                <ResultSection title="SSA Code" content={result.ssa} />
                <ResultSection title="SMT Code" content={result.smt} />
                <ResultSection
                  title="SMT Result"
                  content={`Status: ${result.status}\n\nModel:\n${result.model}`}
                />
              </>
            ) : (
              <>
                <ResultSection title="First Program SSA" content={result.program1.ssa} />
                <ResultSection title="Second Program SSA" content={result.program2.ssa} />
                <ResultSection title="Combined SMT Code" content={result.combined_smt} />
                <ResultSection
                  title="Equivalence Result"
                  content={`Status: ${result.status}\n\nModel:\n${result.model}`}
                />
              </>
            )}
          </div>
        )}
      </div>
    </div>
  );
}

function ResultSection({ title, content }) {
  return (
    <div>
      <h2 className="text-xl font-semibold text-gray-800 mb-2">{title}</h2>
      <pre className="bg-gray-50 p-4 rounded-md overflow-x-auto font-mono text-sm whitespace-pre-wrap">
        {content}
      </pre>
    </div>
  );
}

export default App;