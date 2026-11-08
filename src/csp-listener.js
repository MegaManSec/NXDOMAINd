(function () {
  document.addEventListener(
    'securitypolicyviolation',
    (e) => {
      try {
        chrome.runtime.sendMessage(
          {
            type: 'cspViolation',
            blockedURL: e.blockedURI || '',
            documentURL: e.documentURI || location.href,
          },
          () => void chrome.runtime.lastError,
        );
      } catch {}
    },
    true,
  );
})();
